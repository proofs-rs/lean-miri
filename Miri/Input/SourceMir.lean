import Miri.Input.Model
import Miri.Input.GenericInstantiationWorld

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

/-- Raw metadata access preserves the body-seed order without type resolution. -/
def metadata (document : ImportDocument) (index : Nat) : Except String Metadata := do
  match ← bodySeed document index with
  | .material body =>
    pure ⟨body.toBodyCore.toBodyMetadata,body.instanceId,body.promotedBodies,materialCallSites body.mir⟩
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

end Miri.Input.SourceMir
