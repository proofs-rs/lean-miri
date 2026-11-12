import Miri.Input.Model
import Miri.Input.GenericInstantiationWorld
import Miri.Input.RuntimeArrayTypes
import Miri.Interpreter.BodyIdentity
import Miri.Input.NoopDropShim
import Miri.Input.FnPointerShim

/-! Immutable body seeds. Metadata inspection never instantiates a template.
Executable MIR is produced only by resolveBody, with errors propagated and no
monomorphic fallback or cross-execution result cache. -/
namespace Miri.Input.SourceMir

structure Metadata extends BodyMetadata where
  instanceId : InstanceId
  promotedBodies : Array PromotedBody
  callSites : Array (Nat × MIR.Operand)

private def bodySeed (document : ImportDocument) (index : Nat) : Except String BodySeed :=
  match document.bodies[index]? with
  | some value => pure value
  | none => .error "canonical body index is absent"

private def templateSource (document : ImportDocument) (index : Nat) : Except String CopyTemplateSource :=
  match document.mirTemplates[index]? with
  | some value => pure value
  | none => .error "generic MIR source template is absent"

/-- Structural/source reference checks, independent of substitutions or layout
queries. These also apply to unused source templates during input validation. -/
def validateTemplate (document : ImportDocument) (source : CopyTemplateSource) : Except String Unit := do
  MirTemplate.validateStructure source.template
  unless source.definitionId < document.definitions.size do throw "MIR template definition is absent"
  let span (id : Nat) : Except String Unit :=
    unless id < document.spans.size do throw "MIR template span is absent"
  let scope (id : Nat) : Except String Unit :=
    unless id < source.sourceScopes.size do throw "MIR template source scope is absent"
  let info (value : MIR.SourceInfo) : Except String Unit := do
    span value.span.id
    scope value.scope
  span source.spanId
  span source.preambleDefSpanId
  unless source.localSources.size == source.template.skeleton.locals.size do
    throw "MIR template local-source count mismatch"
  for value in source.localSources do
    span value.spanId
    scope value.scope
  for (value,index) in source.sourceScopes.zipIdx do
    unless value.id == index do throw "MIR template source scopes are not contiguous"
    unless value.inlined.isNone do throw "MIR copy template excludes inlined instance scopes"
    span value.spanId
    for parent in value.parent.toArray ++ value.inlinedParent.toArray do scope parent
  for value in source.backtraceSpans do
    span value.spanId
    unless value.position.filename < document.files.size do throw "MIR template backtrace file is absent"
  for block in source.template.skeleton.blocks do
    for statement in block.statements do info statement.source
    info block.terminator.source
    if let .call _ constantSpan arguments _ _ _ _ functionSpan := block.terminator.kind then
      span constantSpan.id
      span functionSpan.id
      for argument in arguments do span argument.span.id

private def materialCallSites (body : MIR.Body) : Array (Nat × MIR.Operand) := Id.run do
  let mut result := #[]
  for (block,index) in body.basicBlocks.zipIdx do
    match block.terminator.kind with
    | .Call function .. | .TailCall function .. => result := result.push (index,function)
    | _ => pure ()
  return result

private def noopDropSource (document : ImportDocument) (reference : NoopDropRef) :
    Except String (InstanceNode × GenericSubstitution.DefinitionTemplate) := do
  let some sourceInstance := document.instances[reference.instanceId]?
    | throw "no-op drop instance is absent"
  unless sourceInstance.id == reference.instanceId do throw "no-op drop instance ID/index mismatch"
  let .Shim (.DropGlue definition none) := sourceInstance.instanceKind
    | throw "no-op drop source requires exact DropGlue(_, None) identity"
  let some definition := document.definitions[definition]?
    | throw "no-op drop signature definition is absent"
  let some material := definition.genericTemplate
    | throw "no-op drop raw signature material is absent"
  let some signature := material.signatureExpression
    | throw "no-op drop definition has no raw signature"
  NoopDropShim.validateSignature signature
  unless sourceInstance.genericArgs.size == material.parameters.size do
    throw "no-op drop signature argument count mismatch"
  for (argument,sort) in sourceInstance.genericArgs.zip material.parameters do
    let actual := match argument with
      | .Type _ => GenericSubstitution.ArgSort.type
      | .Lifetime _ => .region
      | .Const _ => .constant
    unless actual == sort do throw "no-op drop signature argument sort mismatch"
  unless reference.sourceSpan.spanId < document.spans.size &&
      reference.sourceSpan.position.filename < document.files.size do
    throw "no-op drop source position is absent"
  pure (sourceInstance,material)

private def fnPointerShimSource (document : ImportDocument) (reference : FnPointerShimRef) :
    Except String (InstanceNode × GenericSubstitution.DefinitionTemplate × FnPointerShim.Direction × TypeId) := do
  let some source := document.instances[reference.instanceId]?
    | throw "FnPtr shim instance source is absent"
  unless source.id == reference.instanceId do throw "FnPtr shim instance ID/index mismatch"
  let (definition,selfType,direction) ← match source.instanceKind with
    | .Shim (.FnPtrAsPtr definition selfType) => pure (definition,selfType,FnPointerShim.Direction.asPointer)
    | .Shim (.FnPtrFromPtr definition selfType) => pure (definition,selfType,FnPointerShim.Direction.fromPointer)
    | _ => throw "FnPtr shim source requires an exact pointer conversion shim kind"
  unless source.genericArgs == #[.Type selfType] do throw "FnPtr shim source arguments differ from Self"
  let some selfNode := document.types[selfType]? | throw "FnPtr shim Self source is absent"
  let .functionPointer _ variables := selfNode.shape | throw "FnPtr shim Self is not a function pointer"
  unless variables.isEmpty do throw "FnPtr shim Self has unsupported bound variables"
  let some definition := document.definitions[definition]? | throw "FnPtr shim method definition is absent"
  let some material := definition.genericTemplate | throw "FnPtr shim raw signature material is absent"
  unless material.parameters == #[.type] && material.signatureExpression.isSome do
    throw "FnPtr shim method requires its one-Self raw generic signature"
  let some nonNull := document.definitions[reference.nonNullDefinition]?
    | throw "FnPtr shim NonNull definition is absent"
  let some nonNullMaterial := nonNull.adtDeclaration | throw "FnPtr shim NonNull declaration is absent"
  unless nonNullMaterial.langItem == some "non_null" do throw "FnPtr shim NonNull source lang item differs"
  unless reference.codeDefinition < document.definitions.size do throw "FnPtr shim Code definition is absent"
  unless reference.sourceSpan.spanId < document.spans.size &&
      reference.sourceSpan.position.filename < document.files.size do throw "FnPtr shim source position is absent"
  pure (source,material,direction,selfType)

private def fnPointerShimMetadata (document : ImportDocument) (index : Nat) (reference : FnPointerShimRef) :
    Except String Metadata := do
  let (source,_,direction,_) ← fnPointerShimSource document reference
  let some defPath := source.defPath | throw "FnPtr shim definition path is absent"
  let span := reference.sourceSpan.spanId
  let (locals,statements) := match direction with | .asPointer => (3,2) | .fromPointer => (2,1)
  let fields : BodyMetadata := {
    definitionId := some source.instanceKind.defId,defPath
    sourcePath := s!"$.bodies[{index}]",spanId := span,preambleDefSpanId := span
    injectionPhase := none
    localSources := Array.replicate locals {spanId := span,scope := 0}
    sourceScopes := #[{id := 0,parent := none,spanId := span,inlined := none,inlinedParent := none}]
    backtraceSpans := #[reference.sourceSpan],callEvidence := #[none]
    nodeFacts := #[Array.replicate (statements + 1) {}],requiredConsts := #[] }
  pure ⟨fields,reference.instanceId,#[],#[]⟩

/-- Raw metadata access preserves the body-seed order without type resolution. -/
def metadata (document : ImportDocument) (index : Nat) : Except String Metadata := do
  match ← bodySeed document index with
  | .material body =>
    pure ⟨body.toBodyCore.toBodyMetadata,body.instanceId,body.promotedBodies,materialCallSites body.mir⟩
  | .fnPointerShim reference => fnPointerShimMetadata document index reference
  | .noopDrop reference =>
    let (sourceInstance,_) ← noopDropSource document reference
    let .Shim (.DropGlue definition none) := sourceInstance.instanceKind
      | throw "no-op drop source identity changed"
    let some defPath := sourceInstance.defPath | throw "no-op drop definition path is absent"
    let span := reference.sourceSpan.spanId
    let fields : BodyMetadata := {
      definitionId := some definition,defPath,
      sourcePath := s!"$.bodies[{index}]",spanId := span,preambleDefSpanId := span,
      injectionPhase := none,
      localSources := Array.replicate 2 {spanId := span,scope := 0},
      sourceScopes := #[{id := 0,parent := none,spanId := span,inlined := none,inlinedParent := none}],
      backtraceSpans := #[reference.sourceSpan],callEvidence := #[none],
      nodeFacts := #[#[{}]],requiredConsts := #[] }
    pure ⟨fields,reference.instanceId,#[],#[]⟩
  | .copyTemplate reference =>
    let source ← templateSource document reference.templateId
    validateTemplate document source
    let some sourceInstance := document.instances.find? (·.id == reference.instanceId)
      | throw "MIR template instance is absent"
    unless decide (sourceInstance.instanceKind = .Item source.definitionId) &&
        decide (sourceInstance.genericArgs = reference.genericArgs) do
      throw "MIR template source/generic arguments disagree with the complete instance"
    unless reference.genericArgs.size == source.template.parameters.size do
      throw "MIR template reference argument count mismatch"
    for (argument,sort) in reference.genericArgs.zip source.template.parameters do
      let actual := match argument with
        | .Type _ => GenericSubstitution.ArgSort.type
        | .Lifetime _ => .region
        | .Const _ => .constant
      unless actual == sort do throw "MIR template reference argument sort mismatch"
    let blocks := source.template.skeleton.blocks
    let fields : BodyMetadata := {
      definitionId := some source.definitionId
      defPath := source.defPath
      sourcePath := s!"$.mir_templates[{reference.templateId}]"
      spanId := source.spanId
      preambleDefSpanId := source.preambleDefSpanId
      injectionPhase := source.injectionPhase
      localSources := source.localSources
      sourceScopes := source.sourceScopes
      backtraceSpans := source.backtraceSpans
      -- Symbolic calls are resolved from source type slots on demand rather
      -- than prepared call answers. No TLS, projected places or dynamic casts
      -- belong to this category; local Place::ty uses declarations.
      callEvidence := blocks.map (fun _ => none)
      nodeFacts := blocks.map (fun block => Array.replicate (block.statements.size + 1) {})
      requiredConsts := #[] }
    pure ⟨fields,reference.instanceId,reference.promotedBodies,#[]⟩

private def lift (result : Except String α) : TypeArena.WorldM α :=
  match result with | .ok value => pure value | .error error => throw error

def resolveBody (document : ImportDocument) (index : Nat) : TypeArena.WorldM BodyCore := do
  match ← lift (bodySeed document index) with
  | .material body => pure body.toBodyCore
  | .copyTemplate reference =>
    let sourceMetadata ← lift (metadata document index)
    let source ← lift (templateSource document reference.templateId)
    let arguments ← lift (GenericInstantiationWorld.ofArguments (← get) 16384 reference.genericArgs)
    let mir ← MirTemplate.instantiate source.template 16384 arguments fun expression => do
      let expression ← lift (MirTemplate.eraseFreeRegions 16384 expression)
      lift (MirTemplate.validateClosed 16384 expression)
      GenericInstantiationWorld.resolveType 16384 expression
    pure { toBodyMetadata := sourceMetadata.toBodyMetadata,mir,instanceId := reference.instanceId }

  | .noopDrop reference =>
    let sourceMetadata ← lift (metadata document index)
    let (sourceInstance,material) ← lift (noopDropSource document reference)
    let arguments ← lift (GenericInstantiationWorld.ofArguments (← get) 16384 sourceInstance.genericArgs)
    lift (material.checkArguments arguments)
    let some signature := material.signatureExpression
      | throw "no-op drop raw signature disappeared"
    let mir ← NoopDropShim.instantiate 16384 signature arguments ⟨reference.sourceSpan.spanId⟩
      (GenericInstantiationWorld.resolveType 16384)
    pure {toBodyMetadata := sourceMetadata.toBodyMetadata,mir,instanceId := reference.instanceId}

  | .fnPointerShim reference =>
    let sourceMetadata ← lift (fnPointerShimMetadata document index reference)
    let (_,material,direction,selfType) ← lift (fnPointerShimSource document reference)
    let some signature := material.signatureExpression | throw "FnPtr shim raw signature disappeared"
    let selfType ← lift (GenericInstantiationWorld.ofType (← get) 16384 selfType)
    let nonNull ← lift ((← get).identity reference.nonNullDefinition)
    let code ← lift ((← get).identity reference.codeDefinition)
    let code := GenericSubstitution.Term.definition .type "foreign" code .nil
    let nonNull := GenericSubstitution.Term.definition .type "adt" nonNull (.cons code .nil)
    let mir ← FnPointerShim.instantiate 16384 direction signature selfType nonNull ⟨reference.sourceSpan.spanId⟩
      (GenericInstantiationWorld.resolveType 16384)
    pure {toBodyMetadata := sourceMetadata.toBodyMetadata,mir,instanceId := reference.instanceId}

/-- Resolve one exact raw body reference. No material table index is inferred
from a constructed identity or from a source template number. -/
private def resolveBodyKey (key : BodyArena.Key) : RuntimeArrayTypes.CompilerM BodyCore := do
  let world ← get
  let document := world.metadata.source
  let verified ← match BodyArena.Key.create world.arena world.instances document.mirTemplates
      key.templateId key.instanceId key.promoted with
    | .ok key => pure key | .error error => throw error
  unless verified == key do throw "body reference contradicts the current compiler universe"
  let index := key.templateId
  let some source := document.mirTemplates[index]? | throw "raw body source disappeared"
  match validateTemplate document source with
  | .error error => throw error | .ok () => pure ()
  let arguments ← match GenericInstantiationWorld.ofArguments world.arena 16384 key.instanceKey.arguments with
    | .ok arguments => pure arguments | .error error => throw error
  let mir ← MirTemplate.instantiate source.template 16384 arguments fun expression => do
    let expression ← match MirTemplate.eraseFreeRegions 16384 expression with
      | .ok expression => pure expression | .error error => throw error
    match MirTemplate.validateClosed 16384 expression with
    | .error error => throw error | .ok () => pure ()
    RuntimeArrayTypes.liftType (GenericInstantiationWorld.resolveType 16384 expression)
  let blocks := source.template.skeleton.blocks
  let bodyMetadata : BodyMetadata := {
    definitionId := some source.definitionId
    defPath := source.defPath
    sourcePath := s!"$.mir_templates[{index}]"
    spanId := source.spanId
    preambleDefSpanId := source.preambleDefSpanId
    injectionPhase := source.injectionPhase
    localSources := source.localSources
    sourceScopes := source.sourceScopes
    backtraceSpans := source.backtraceSpans
    callEvidence := blocks.map (fun _ => none)
    nodeFacts := blocks.map (fun block => Array.replicate (block.statements.size + 1) {})
    requiredConsts := #[] }
  pure {toBodyMetadata := bodyMetadata,mir,instanceId := key.instanceId}

private def shimKeyMetadata (key : BodyArena.ShimKey) : RuntimeArrayTypes.CompilerM Metadata := do
  let world ← get
  let document := world.metadata.source
  let verified ← match BodyArena.ShimKey.create world.arena world.instances document.instances key.source key.instanceId with
    | .ok key => pure key | .error error => throw error
  unless verified == key do throw "shim body reference contradicts current compiler universe"
  let some index := document.bodies.findIdx? (fun seed => match seed with
      | .fnPointerShim source => source == key.source | _ => false)
    | throw "raw shim body recipe is absent from immutable source"
  let metadata ← match fnPointerShimMetadata document index key.source with
    | .ok metadata => pure metadata | .error error => throw error
  pure {metadata with instanceId := key.instanceId}

private def resolveShimKey (key : BodyArena.ShimKey) : RuntimeArrayTypes.CompilerM BodyCore := do
  let metadata ← shimKeyMetadata key
  let document := (← get).metadata.source
  let (_,material,direction,_) ← match fnPointerShimSource document key.source with
    | .ok source => pure source | .error error => throw error
  let selfType ← match key.instanceKey.kind with
    | .Shim (.FnPtrAsPtr _ selfType) | .Shim (.FnPtrFromPtr _ selfType) => pure selfType
    | _ => throw "FnPtr shim body key lost its exact kind"
  let mir ← RuntimeArrayTypes.liftType do
    let some signature := material.signatureExpression | throw "FnPtr shim raw signature disappeared"
    let selfType ← lift (GenericInstantiationWorld.ofType (← get) 16384 selfType)
    let nonNull ← lift ((← get).identity key.source.nonNullDefinition)
    let code ← lift ((← get).identity key.source.codeDefinition)
    let code := GenericSubstitution.Term.definition .type "foreign" code .nil
    let nonNull := GenericSubstitution.Term.definition .type "adt" nonNull (.cons code .nil)
    FnPointerShim.instantiate 16384 direction signature selfType nonNull ⟨key.source.sourceSpan.spanId⟩
      (GenericInstantiationWorld.resolveType 16384)
  pure {toBodyMetadata := metadata.toBodyMetadata,mir,instanceId := key.instanceId}

private def validateMaterialBodyInstance (world : RuntimeArrayTypes.World) (index : Nat) : Except String Unit := do
  let some seed := world.metadata.source.bodies[index]? | throw "material body source is absent"
  let some expected := world.metadata.source.instances[seed.instanceId]?
    | throw "material body instance source is absent"
  let expected ← InstanceArena.Key.ofSource world.arena expected.instanceKind expected.genericArgs
  let actual ← match ← world.instances.lookup seed.instanceId with
    | .material key | .constructed key => pure key
  unless actual == expected do throw "material body source differs from execution instance store"

/-- Runtime body identities always dispatch through this execution's body
universe. The immutable body array is addressed only after a material lookup. -/
def resolveBodyIdentity (identity : Miri.Interpreter.BodyIdentity) :
    RuntimeArrayTypes.CompilerM BodyCore := do
  let world ← get
  let view ← match world.bodies.lookup identity.index with
    | .ok view => pure view | .error error => throw error
  match view with
  | .material index =>
    match validateMaterialBodyInstance world index with
    | .ok () => pure () | .error error => throw error
    RuntimeArrayTypes.liftType (resolveBody world.metadata.source index)
  | .constructed (.template key) => resolveBodyKey key
  | .constructed (.fnPointerShim key) => resolveShimKey key


/-- Type-free metadata for an exact runtime body identity. The return type does
not claim a promoted-body catalog or instantiate source local types. -/
def metadataIdentity (identity : Miri.Interpreter.BodyIdentity) :
    RuntimeArrayTypes.CompilerM BodyMetadata := do
  let world ← get
  let document := world.metadata.source
  let view ← match world.bodies.lookup identity.index with
    | .ok view => pure view | .error error => throw error
  match view with
  | .material index =>
    match validateMaterialBodyInstance world index with
    | .ok () => pure () | .error error => throw error
    match metadata document index with
    | .ok value => pure value.toBodyMetadata | .error error => throw error
  | .constructed (.fnPointerShim key) => return (← shimKeyMetadata key).toBodyMetadata
  | .constructed (.template key) =>
    let verified ← match BodyArena.Key.create world.arena world.instances document.mirTemplates
        key.templateId key.instanceId key.promoted with
      | .ok key => pure key | .error error => throw error
    unless verified == key do throw "metadata body reference contradicts the compiler universe"
    let some source := document.mirTemplates[key.templateId]? | throw "raw body source disappeared"
    match validateTemplate document source with
    | .error error => throw error | .ok () => pure ()
    pure {
      definitionId := some source.definitionId
      defPath := source.defPath
      sourcePath := s!"$.mir_templates[{key.templateId}]"
      spanId := source.spanId
      preambleDefSpanId := source.preambleDefSpanId
      injectionPhase := source.injectionPhase
      localSources := source.localSources
      sourceScopes := source.sourceScopes
      backtraceSpans := source.backtraceSpans
      callEvidence := source.template.skeleton.blocks.map (fun _ => none)
      nodeFacts := source.template.skeleton.blocks.map (fun block => Array.replicate (block.statements.size + 1) {})
      requiredConsts := #[] }

end Miri.Input.SourceMir
