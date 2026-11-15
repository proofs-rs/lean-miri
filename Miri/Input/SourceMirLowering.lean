import Miri.Input.SourceMirReferences
import Miri.Input.SourceMirRvalues
import Miri.Input.SourceCompilerAllocations
import Miri.Input.Model.SourceMir
import Miri.Input.SourceAbi
import Miri.Input.SourceCompilerWorldAbi
import Miri.Input.LowerMIR

/-! Demand-time typed source MIR lowering. IDs are allocated only in the current
World. Unsupported syntax is rejected, never erased or changed to a no-op. -/
namespace Miri.Input.SourceMirLowering
open Miri.Interpreter
abbrev World := SourceCompilerWorld.World

private def known (value : SourceMir.Operator α) : Except String α :=
  match value with | .known value => pure value | .unsupported tag => throw s!"Unsupported source MIR operator {tag}"
private def phase : SourceMir.Phase → Except String MIR.MirPhase
  | .known value => pure value | .unsupported tag => throw s!"Unsupported source MIR phase {tag}"

private structure Context where
  source : SourceMir.Body
  types : Array (Option Nat)
  spans : Array Nat
  world : World
  localTypes : Array Nat
  definitions : Array (Option Nat)
  allocations : Array (Nat × Nat)
  requests : Array (SourceMir.Constant × Nat)

private def span (c : Context) (id : Nat) : Except String Nat := do
  let some id := c.spans[id]? | throw "Invalid source MIR span reference"
  return id
private def info (c : Context) (source : SourceMir.SourceInfo) : Except String MIR.SourceInfo := do
  return ⟨⟨← span c source.span⟩,source.scope⟩
private def constant (c : Context) (value : SourceMir.Constant) : Except String MIR.ConstOperand := do
  -- User type annotations are type-checking metadata. The pinned runtime
  -- evaluates const_ and span only; retain the opaque source index unchanged.
  let some type := c.types[value.type]?.join | throw "Unsupported source MIR constant type not yet instantiated"
  let matching :=  c.source.spans.filter (·.key == value.span)
  let [sourceSpan] := matching.toList | throw "Invalid source MIR constant span identity absent/ambiguous"
  let allocation (source : Nat) : Except String Nat := do
    let some (_,id) := c.allocations.find? (·.1 == source)
      | throw "source constant allocation demand missing"
    pure id
  if let .unevaluated .. := value.value then
    let some (_,token) := c.requests.find? (·.1 == value)
      | throw "Invalid source constant request was not registered"
    return ⟨⟨← span c sourceSpan.identity⟩,value.userType,.SourceRequest token type⟩
  let value' ← match value.value with
    | .zeroSized => pure MIR.ConstValue.ZeroSized
    | .scalar bits bytes => pure (.Scalar (.Int bits bytes))
    | .allocationSlice source metadata => pure (.Slice (← allocation source) metadata)
    | .allocationIndirect source offset => pure (.Indirect (← allocation source) offset)
    | .allocationPointer source offset immutable sharedRef =>
      pure (.Scalar (.Ptr (.Allocation (← allocation source) offset immutable sharedRef)))
    | _ => throw "Unsupported typed source constant evaluation"
  return ⟨⟨← span c sourceSpan.identity⟩,value.userType,.Val value' type⟩
private def rvalueContext (c : Context) : SourceMirRvalues.Context :=
  ⟨c.world,c.localTypes,c.types,c.definitions,constant c⟩
private def facts (values : Array PlaceFact) : Except String NodeFacts := do
  let mut places := #[]
  for value in values do
    if let some prior := places.find? (fun p : PlaceFact => p.place == value.place) then
      unless prior.typeId == value.typeId && prior.projectionTypes == value.projectionTypes do
        throw "Invalid source projection facts conflict"
    else places := places.push value
  return {places}
private def statement (c : Context) (s : SourceMir.Statement) : Except String (MIR.Statement × NodeFacts) := do
  let (kind,places) ← match s.kind with
    | .assign destination value => do
      let (destination,p) ← SourceMirRvalues.place (rvalueContext c) destination
      let (value,places) ← SourceMirRvalues.lower (rvalueContext c) p.typeId value
      pure (MIR.StatementKind.Assign destination value,#[p] ++ places)
    | .storageLive id => pure (.StorageLive id,#[])
    | .storageDead id => pure (.StorageDead id,#[])
    | .placeMention place => do
      let (place,fact) ← SourceMirRvalues.place (rvalueContext c) place
      pure (.PlaceMention place,#[fact])
    | .nop => pure (.Nop,#[])
    | .unsupported tag => throw s!"Unsupported source MIR statement {tag}"
  return (⟨← info c s.source,kind⟩,← facts places)
private def unwind : SourceMir.Unwind → Except String MIR.UnwindAction
  | .continueUnwind => pure .Continue
  | .unreachable => pure .Unreachable
  | .cleanup target => pure (.Cleanup target)
  | .terminate reason => return .Terminate (← known reason)
  | .unsupported tag => throw s!"Unsupported source MIR unwind {tag}"
private def terminator (c : Context) (t : SourceMir.Terminator) : Except String (MIR.Terminator × NodeFacts) := do
  let (kind,places) ← match t.kind with
    | .returnValue => pure (MIR.TerminatorKind.Return,#[])
    | .goto target => pure (.Goto target #[],#[])
    | .resumeUnwind => pure (.UnwindResume,#[])
    | .terminateUnwind reason => pure (.UnwindTerminate (← known reason),#[])
    | .unreachable => pure (.Unreachable,#[])
    | .switchInt op values otherwise => do
      let (op,_,places) ← SourceMirRvalues.operand (rvalueContext c) op
      pure (.SwitchInt op ⟨values.map (fun (v,b) => .Case v b),otherwise⟩,places)
    | .assert condition expected message target action => do
      let (condition,_,a) ← SourceMirRvalues.operand (rvalueContext c) condition
      let (message,b) ← SourceMirRvalues.assertion (rvalueContext c) message
      pure (.Assert condition expected message target (← unwind action),a ++ b)
    | .call function arguments destination target action source functionSpan => do
      let (function,_,places) ← SourceMirRvalues.operand (rvalueContext c) function
      let mut places := places
      let mut args := #[]
      for argument in arguments do
        let (value,_,extra) ← SourceMirRvalues.operand (rvalueContext c) argument.operand
        args := args.push (MIR.SpannedOperand.mk ⟨← span c argument.span⟩ value)
        places := places ++ extra
      let (destination,extra) ← SourceMirRvalues.place (rvalueContext c) destination
      pure (.Call function args destination target (← unwind action) (← known source) ⟨← span c functionSpan⟩,
        places.push extra)
    | .drop value target action replace asyncDrop => do
      let (value,p) ← SourceMirRvalues.place (rvalueContext c) value
      pure (.Drop value target (← unwind action) replace asyncDrop,#[p])
    | .unsupported tag => throw s!"Unsupported source MIR terminator {tag}"
  return (⟨← info c t.source,kind⟩,← facts places)

/-- Install one genuine typed body. Existing canonical rows retain their IDs.
No compiler function/allocation identity is inferred from these local handles. -/
def derive (initial : World) (callee : CallInstance) : Except String World := do
  let node ← SourceCompilerWorld.node initial callee
  if node.kind == .instanceMir then
    let _ ← SourceCompilerWorld.bodyId initial callee
    return initial
  let key ← SourceCompilerWorld.keyOf initial callee
  let some material := initial.canonical.sourceMaterial | throw "Unsupported source MIR material absent"
  let some mir := material.genericMir | throw "Unsupported typed source MIR unavailable"
  let [body] := (mir.bodies.filter fun b => b.definition == key.definition && b.promoted.isNone).toList
    | throw s!"Unsupported source MIR body absent/ambiguous: {reprStr key.definition}; {node.defPath.getD "<unknown>"}"
  unless body.promotedCount == 0 do throw "Unsupported source MIR promoted body installation"
  let some _ := material.physical | throw "Unsupported typed source MIR type expressions unavailable"
  let parameters ← SourceDeclarations.fullParameters material.genericLayers key.definition
  unless parameters.size == key.arguments.size do throw "Invalid source MIR substitution count"
  let mut typeArguments := #[]
  let mut constArguments := #[]
  for (parameter,arg) in parameters.zip key.arguments do
    match parameter,arg with
    | .typeParameter,.Type id =>
      typeArguments := typeArguments.push (some (← SourceConcreteTypes.concreteType initial material.target.pointerSizeBits id))
      constArguments := constArguments.push none
    | .region,.Lifetime _ =>
      typeArguments := typeArguments.push none; constArguments := constArguments.push none
    | _,_ => throw "Unsupported typed source MIR generic constant substitution"
  -- Derivation also checks the source signature and its inherited obligations.
  let (initial,abi) ← SourceAbi.derive initial callee #[]
  let (initial,_) ← SourceCompilerWorld.attachInstanceAbi initial callee #[] abi
  let mut world := initial
  let root := mir.rootSpan
  let rootId := world.canonical.queries.session.rootSpan
  let some rootData := world.canonical.spans[rootId]? | throw "Invalid canonical source session root span"
  unless world.canonical.files[rootData.file]? == some root.file &&
      rootData == ⟨root.isDummy,root.key.lo,root.key.hi,⟨root.startLine,root.startColumn⟩,
        ⟨root.endLine,root.endColumn⟩,root.key.context,rootData.file⟩ do
    throw "Invalid typed MIR/canonical session root span mismatch"
  if let some (_,existing) := world.derivedSourceSpans.find? (·.1 == root.key) then
    unless existing == rootId do throw "Invalid source session root identity conflict"
  else world := {world with derivedSourceSpans := world.derivedSourceSpans.push (root.key,rootId)}
  let mut types := #[]
  let (prepared,referencePool) ← SourceMirReferences.prepare world body typeArguments constArguments
  world := prepared
  let mut allocations : Array (Nat × Nat) := #[]
  for source in referencePool.allocations do
    unless allocations.any (·.1 == source) do
      let (updated,id) ← SourceCompilerAllocations.demand world source
      world := updated
      allocations := allocations.push (source,id)
  let typeMap := referencePool.types
  let mut requests := #[]
  for value in referencePool.constants do
    if let .unevaluated definition arguments promoted := value.value then
      let some expected := typeMap[value.type]?.join | throw "Invalid source constant request type absent"
      let (updated,token) ← SourceCompilerWorld.internConstantRequest world callee definition arguments
        promoted typeArguments constArguments expected
      world := updated
      requests := requests.push (value,token)
  for source in body.locals do
    let some id := typeMap[source.type]?.join | throw "Invalid source MIR local type absent"
    types := types.push id
  unless body.spreadArgument.isNone && body.argumentCount == abi.arguments.size &&
      types[0]? == some abi.returnValue.typeId do throw "Invalid source MIR signature/return local mismatch"
  for (argument,index) in abi.arguments.zipIdx do
    unless types[index+1]? == some argument.typeId do throw "Invalid source MIR argument local/signature mismatch"
  let mut spanIds := #[]
  for source in body.spans do
    unless source.identity == spanIds.size do throw "Invalid source MIR span identity order"
    let file := (world.canonical.files.findIdx? (· == source.file)).getD world.canonical.files.size
    let files := if file == world.canonical.files.size then world.canonical.files.push source.file else world.canonical.files
    let row : SourceSpanData := ⟨source.isDummy,source.key.lo,source.key.hi,
      ⟨source.startLine,source.startColumn⟩,⟨source.endLine,source.endColumn⟩,source.key.context,file⟩
    let id ← if let some (_,id) := world.derivedSourceSpans.find? (·.1 == source.key) then do
      unless world.canonical.spans[id]? == some row do throw "Invalid source span identity/payload conflict"
      pure id
    else do
      let id := world.canonical.spans.size
      world := {world with
        derivedSourceSpans := world.derivedSourceSpans.push (source.key,id)
        canonical := {world.canonical with files,spans := world.canonical.spans.push row}}
      pure id
    spanIds := spanIds.push id
  let c : Context := ⟨body,typeMap,spanIds,world,types,referencePool.definitions,allocations,requests⟩
  let mut blocks := #[]
  let mut nodeFacts := #[]
  for b in body.blocks do
    let statements ← b.statements.mapM (statement c)
    let (terminator,fact) ← terminator c b.terminator
    blocks := blocks.push ⟨statements.map (·.1),terminator,b.cleanup⟩
    nodeFacts := nodeFacts.push ((statements.map (·.2)).push fact)
  let sourceScopes ← body.scopes.mapIdxM fun id s => do
    return SourceScope.mk id s.parent (← span c s.span) none s.inlinedParent
  let mut backtraceSpans := #[]
  for b in body.backtraces do
    let file := (world.canonical.files.findIdx? (· == b.filename)).getD world.canonical.files.size
    if file == world.canonical.files.size then
      world := {world with canonical := {world.canonical with files := world.canonical.files.push b.filename}}
    backtraceSpans := backtraceSpans.push ⟨← span c b.span,⟨b.bytePosition,b.line,b.column,file⟩⟩
  let localSources ← body.locals.mapM fun l => do
    return SourceInfo.mk (← span c l.source.span) l.source.scope
  let bodyId := world.canonical.bodies.size
  let actual : Input.Body := {
    mir := ⟨← phase body.phase,body.argumentCount,body.spreadArgument,types,blocks⟩,
    definitionId := node.definitionId, defPath := node.defPath.getD "", sourcePath := s!"source.mir[{bodyId}]",
    spanId := ← span c body.bodySpan,preambleDefSpanId := ← span c body.definitionSpan,
    injectionPhase := ← body.injectionPhase.mapM phase,instanceId := callee,
    localSources,sourceScopes,backtraceSpans,callEvidence := Array.replicate blocks.size none,
    nodeFacts,
    requiredConsts := ← body.requiredConstants.mapM (constant c),promotedBodies := #[] }
  LocalValidation.validateBody actual s!"source.bodies[{bodyId}]"
  let lowered ← lowerBody (LowerContext.ofDocument world.canonical) actual.toBodyCore
  unless lowered.obligations.isEmpty do throw "Unsupported source MIR lowering obligations"
  let some _ := world.canonical.instances[callee]? | throw "Invalid source MIR instance disappeared"
  let updated := {node with kind := .instanceMir,bodyId := some bodyId}
  return {world with canonical := {world.canonical with
    bodies := world.canonical.bodies.push actual
    instances := world.canonical.instances.setIfInBounds callee updated}}
end Miri.Input.SourceMirLowering
