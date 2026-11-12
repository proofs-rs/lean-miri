import Miri.Input.Model
import Miri.Input.DecodeMIR
import Miri.Input.TypeArena

namespace Miri.Input

abbrev LowerResult := Except String

structure LowerContext where
  spans : Array SourceSpanData := #[]
  layouts : Array Layout := #[]
  definitions : Array DefinitionId := #[]
  instances : Array InstanceNode := #[]
  typeConstants : Array MIR.TypeConst := #[]
  typeIds : Array TypeId
  lazyTypeNodes : Option (Array TypeNode) := none
  allocationIds : Array AllocationId := #[]
  obligations : Array Obligation := #[]

def LowerContext.containsTypeId (ctx : LowerContext) (id : TypeId) : Bool :=
  ctx.typeIds.contains id || match ctx.lazyTypeNodes with
    | some nodes => (TypeArena.node nodes id).isOk
    | none => false

def LowerContext.containsAllocationId (ctx : LowerContext) (id : AllocationId) : Bool := ctx.allocationIds.contains id

def LowerContext.withTypeIds (ctx : LowerContext) (ids : Array TypeId) : LowerContext := {ctx with typeIds := ids, lazyTypeNodes := none}
/-- Enable lazy constructor identities only in runtime compiler contexts.
Source MIR lowering retains strict material-pool bounds. -/
def LowerContext.withLazyTypes (ctx : LowerContext) (nodes : Array TypeNode) : LowerContext :=
  {ctx with lazyTypeNodes := some nodes}
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

structure LoweredProgram where
  bundle : LoweredBodies
  /-- Root body indices into `bundle.bodies`, in the original document order. -/
  roots : Array Nat
  /-- Instance graph identity to body index; the source graph is retained below. -/
  instances : Array (InstanceId × Nat)
  /-- (parent body index, promoted index, body index). -/
  promoted : Array (Nat × Nat × Nat)
  input : ImportDocument

/-- Look up a document root's frame identity without assuming it was called
or that source and runtime definition indices coincide. -/
def LoweredProgram.rootDefinitionId (program : LoweredProgram) (rootIndex : Nat)
    : LowerResult MIR.DefId := do
  let some bodyIndex := program.roots[rootIndex]? | throw "root index is out of range"
  let some body := program.bundle.bodies[bodyIndex]? | throw "root body index is out of range"
  body.ownDefinitionId

/-- Lower all present root, instance, and promoted bodies with global compiler
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
  for (body, bodyId) in input.bodies.toList.zipIdx do
    for child in body.promotedBodies do
      if let some childId := child.bodyId then
        unless childId < input.bodies.size do throw s!"missing promoted body {childId}"
        let entry := (bodyId, child.index, childId)
        unless promoted.contains entry do promoted := promoted.push entry
  pure ⟨← lowerBodies (LowerContext.ofDocument input) (input.bodies.map Body.toBodyCore),
    roots, instances, promoted, input⟩



structure CompilerTables where
  spans : Array SourceSpanData
  definitions : Array DefinitionId
  typeConstants : Array MIR.TypeConst

def LoweredProgram.compilerTables (program : LoweredProgram) : CompilerTables :=
  ⟨program.bundle.spans, program.bundle.definitions, program.bundle.typeConstants⟩

def LoweredProgram.withCompilerTables (program : LoweredProgram) (tables : CompilerTables) : LoweredProgram :=
  let bodies := program.bundle.bodies.map fun body => { body with
    spans := tables.spans, definitions := tables.definitions, typeConstants := tables.typeConstants }
  { program with bundle := ⟨bodies, tables.spans, tables.definitions, tables.typeConstants⟩ }

def lowerCompilerSpan (tables : CompilerTables) (value : MIR.SpanRef) :
    LowerResult (MIR.SpanRef × CompilerTables) := do
  unless value.id < tables.spans.size do throw s!"missing span {value.id}"
  pure (value,tables)

end Miri.Input
