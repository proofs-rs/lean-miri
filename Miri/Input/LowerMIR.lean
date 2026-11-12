import Miri.Input.Model
import Miri.Input.DecodeMIR
import Miri.Input.TypeArenaWorld
import Miri.Input.SourceMir

namespace Miri.Input

abbrev LowerResult := Except String

structure LowerContext where
  spans : Array SourceSpanData := #[]
  layouts : Array Layout := #[]
  definitions : Array DefinitionId := #[]
  instances : Array InstanceNode := #[]
  typeConstants : Array MIR.TypeConst := #[]
  typeIds : Array TypeId
  typeUniverse : Option TypeArena.World := none
  allocationIds : Array AllocationId := #[]
  obligations : Array Obligation := #[]

def LowerContext.containsTypeId (ctx : LowerContext) (id : TypeId) : Bool :=
  ctx.typeIds.contains id || match ctx.typeUniverse with
    | some world => (world.lookupType id).isOk
    | none => false

def LowerContext.containsAllocationId (ctx : LowerContext) (id : AllocationId) : Bool := ctx.allocationIds.contains id

def LowerContext.withTypeIds (ctx : LowerContext) (ids : Array TypeId) : LowerContext := {ctx with typeIds := ids, typeUniverse := none}
/-- Bind lowering to the actual execution's persistent constructor universe. -/
def LowerContext.withWorld (ctx : LowerContext) (world : TypeArena.World) : LowerContext :=
  {ctx with typeUniverse := some world}
def LowerContext.withAllocationIds (ctx : LowerContext) (ids : Array AllocationId) : LowerContext := {ctx with allocationIds := ids}
def LowerContext.ofTypes (types : Array TypeNode) : LowerContext :=
  {typeIds := types.map (·.id)}

def LowerContext.ofDocument (document : ImportDocument) : LowerContext :=
  {LowerContext.ofTypes document.types with
    allocationIds := document.allocations.map (·.id), spans := document.spans,
    layouts := document.layouts, definitions := document.definitions,
    instances := document.instances, typeConstants := document.typeConstants}

structure LoweredBody where
  spans : Array SourceSpanData
  input : BodyCore
  definitions : Array DefinitionId
  typeConstants : Array MIR.TypeConst
  obligations : Array Obligation

def LoweredBody.body (body : LoweredBody) : MIR.Body := body.input.mir

def lookupDefinitionId (definitions : Array DefinitionId) (id : Nat) : LowerResult MIR.DefId := do
  unless id < definitions.size do throw s!"unresolved compiler definition {id}"
  pure id

def LoweredBody.ownDefinitionId (body : LoweredBody) : LowerResult MIR.DefId := do
  let some id := body.input.definitionId | throw "body is missing its source definition identity"
  lookupDefinitionId body.definitions id

def lowerBody (ctx : LowerContext) (input : BodyCore) : LowerResult LoweredBody :=
  let obligations := if input.definitionId.isSome then ctx.obligations else
    ctx.obligations.push ⟨"body.definitionId", "source definition identity is missing; runtime frame initialization must fail until supplied"⟩
  pure ⟨ctx.spans, input, ctx.definitions, ctx.typeConstants, obligations⟩

structure LoweredBodies where
  bodies : Array LoweredBody
  spans : Array SourceSpanData
  definitions : Array DefinitionId
  typeConstants : Array MIR.TypeConst

def lowerBodies (ctx : LowerContext) (inputs : Array BodyCore) : LowerResult LoweredBodies := do
  pure ⟨← inputs.mapM (lowerBody ctx), ctx.spans, ctx.definitions, ctx.typeConstants⟩

structure CompilerTables where
  spans : Array SourceSpanData
  definitions : Array DefinitionId
  typeConstants : Array MIR.TypeConst

structure LoweredProgram where
  bundle : CompilerTables
  /-- Root body indices into the source body-seed table, in the original document order. -/
  roots : Array Nat
  /-- Instance graph identity to body index; the source graph is retained below. -/
  instances : Array (InstanceId × Nat)
  /-- (parent body index, promoted index, body index). -/
  promoted : Array (Nat × Nat × Nat)
  input : ImportDocument

/-- Source body count; preparation never constructs an executable MIR vector. -/
def LoweredProgram.bodyCount (program : LoweredProgram) : Nat := program.input.bodies.size

def LoweredProgram.bodyMetadata (program : LoweredProgram) (index : Nat) :
    LowerResult SourceMir.Metadata := SourceMir.metadata program.input index

/-- Instantiate and lower only the actual body requested by a runtime operation.
No instantiated result is cached in the immutable compilation input. -/
def LoweredProgram.resolveBody (program : LoweredProgram) (index : Nat) :
    TypeArena.WorldM LoweredBody := do
  let source ← SourceMir.resolveBody program.input index
  -- Body wrapping needs only these immutable tables. Constructing the full
  -- source reference indexes here would scan every type/allocation on each
  -- runtime frame/debug lookup without contributing to lowerBody.
  let ctx : LowerContext := {
    spans := program.bundle.spans, definitions := program.bundle.definitions,
    typeConstants := program.bundle.typeConstants, typeIds := #[]}
  let ctx ← match program.input.bodies[index]? with
    | some (.material _) => pure ctx
    | some (.copyTemplate _) => do
      let ctx := ctx.withWorld (← get)
      for ty in source.mir.locals do
        unless ctx.containsTypeId ty do throw "instantiated MIR local type is absent from its runtime type universe"
      pure ctx
    | none => throw "canonical body index is absent"
  match lowerBody ctx source with
  | .ok body => pure body
  | .error error => throw error

/-- The minimal runtime body context preserves every field observed by
lowerBody; source reference indexes are validated separately at import. -/
theorem lowerBody_minimalContext (document : ImportDocument) (tables : CompilerTables)
    (source : BodyCore) :
    lowerBody {LowerContext.ofDocument document with
      spans := tables.spans, definitions := tables.definitions,
      typeConstants := tables.typeConstants} source =
    lowerBody {
      spans := tables.spans, definitions := tables.definitions,
      typeConstants := tables.typeConstants, typeIds := #[]} source := by
  rfl

/-- Look up a document root's frame identity without assuming it was called
or that source and runtime definition indices coincide. -/
def LoweredProgram.rootDefinitionId (program : LoweredProgram) (rootIndex : Nat)
    : LowerResult MIR.DefId := do
  let some bodyIndex := program.roots[rootIndex]? | throw "root index is out of range"
  let source ← program.bodyMetadata bodyIndex
  let some definition := source.definitionId | throw "body is missing its source definition identity"
  lookupDefinitionId program.bundle.definitions definition

/-- Retain raw body seeds and root, instance, and promoted identities with global compiler
identity tables. Unavailable bodies remain explicit source graph obligations. -/
def lowerProgram (input : ImportDocument) : LowerResult LoweredProgram := do
  let mut roots := #[]
  let mut instances := #[]
  let mut promoted := #[]
  for root in input.bodyRoots do
    unless root.bodyId < input.bodies.size do throw s!"missing root body {root.bodyId}"
    roots := roots.push root.bodyId
    for child in root.promotedBodies do
      if let some bodyId := child.bodyId then
        unless bodyId < input.bodies.size do throw s!"missing promoted body {bodyId}"
        promoted := promoted.push (root.bodyId, child.index, bodyId)
  for inst in input.instances do
    if let some bodyId := inst.bodyId then
      unless bodyId < input.bodies.size do throw s!"missing instance body {bodyId}"
      instances := instances.push (inst.id, bodyId)
      for child in inst.promotedBodies do
        if let some childId := child.bodyId then
          unless childId < input.bodies.size do throw s!"missing promoted body {childId}"
          promoted := promoted.push (bodyId, child.index, childId)
  for bodyId in [:input.bodies.size] do
    let source ← SourceMir.metadata input bodyId
    for child in source.promotedBodies do
      if let some childId := child.bodyId then
        unless childId < input.bodies.size do throw s!"missing promoted body {childId}"
        let entry := (bodyId, child.index, childId)
        unless promoted.contains entry do promoted := promoted.push entry
  pure ⟨⟨input.spans,input.definitions,input.typeConstants⟩,
    roots, instances, promoted, input⟩



def LoweredProgram.compilerTables (program : LoweredProgram) : CompilerTables :=
  program.bundle

def LoweredProgram.withCompilerTables (program : LoweredProgram) (tables : CompilerTables) : LoweredProgram :=
  {program with bundle := tables}

def lowerCompilerSpan (tables : CompilerTables) (value : MIR.SpanRef) :
    LowerResult (MIR.SpanRef × CompilerTables) := do
  unless value.id < tables.spans.size do throw s!"missing span {value.id}"
  pure (value,tables)

end Miri.Input
