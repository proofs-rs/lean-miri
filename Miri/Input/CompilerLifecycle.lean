import Miri.Input.SourceCompilerConstantRequests
import Miri.Input.SourceCompilerWorld
import Miri.Input.CompilerInstance
import Miri.Interpreter.CallMachine

/-! The resolved body identifies its concrete callee and preamble span.
Concrete legacy constants were evaluated before export. Source required constants
resolve compiler witnesses at frame entry through the same World as operands. -/
namespace Miri.Input.CompilerLifecycle
open Lean Miri.Interpreter
structure Entry where
  preamble : Except String MIR.SpanRef
  callee : Except String CallInstance
structure Prepared where
  program : LoweredProgram
  entries : Array Entry

def prepare (program : LoweredProgram) : Prepared := Id.run do
  let ctx := LowerContext.ofDocument program.input
  let mut tables := program.compilerTables
  let mut entries := #[]
  for body in program.bundle.bodies do
    let preamble := do
      lowerCompilerSpan tables ⟨body.input.preambleDefSpanId⟩
    let preamble ← match preamble with
      | .error error => pure (.error error)
      | .ok (span,next) =>
        tables := next
        pure (.ok span)
    let decoded : Except String (CallInstance × CompilerTables) := do
      unless body.input.instanceId < ctx.instances.size do throw "body instance ID out of bounds"
      pure (body.input.instanceId,tables)
    let callee ← match decoded with
      | .error error => pure (.error error)
      | .ok (callee,next) =>
        tables := next
        pure (.ok callee)
    entries := entries.push ⟨preamble,callee⟩
  return ⟨program.withCompilerTables tables,entries⟩

private def lift (query : Except String A) : MachineHooks.M K User A :=
  match query with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler lifecycle: {error}")
private def entry (p : Prepared) (body : LoadedBody) : Except String Entry := do
  let some actual := p.program.bundle.bodies[body.identity.index]? | throw "canonical body identity absent"
  unless actual.body == body.body do throw "canonical body identity/content mismatch"
  let some entry := p.entries[body.identity.index]? | throw "body lifecycle evidence absent"
  return entry

def preambleSpan (p : Prepared) (body : LoadedBody) : MachineHooks.M K User MIR.SpanRef :=
  lift do (← entry p body).preamble

def requiredConstants (p : Prepared) (body : LoadedBody) : MachineHooks.M K User Unit := do
  let entry ← lift (entry p body)
  let callee ← lift entry.callee
  let frame ← MachineHooks.currentFrame
  unless frame.bodyIdentity == body.identity && frame.functionInstance == callee do
    throw (.invalidProgram "required-constant current frame identity/instance mismatch")
  pure ()

/-- Metadata for a body installed after preparation is read from the same live
World that supplied its LoadedBody. It is never recovered by structural search. -/
private def currentBody (world : SourceCompilerWorld.World) (body : LoadedBody) :
    Except String Body := do
  let some actual := world.canonical.bodies[body.identity.index]?
    | throw "canonical body identity absent"
  let identity ← SourceCompilerWorld.bodyId world actual.instanceId
  unless identity == body.identity.index && actual.mir == body.body do
    throw "canonical body identity/content mismatch"
  return actual

private def currentWorld (access : SourceCompilerWorld.Access (MachineHooks.State K User)) :
    MachineHooks.M K User SourceCompilerWorld.World := do
  let some world := access.get (← get)
    | throw (.unsupported "compiler lifecycle: source compiler World unavailable")
  return world

/-- Exact current canonical preamble metadata, independent of preparation. -/
def sourcePreambleSpan (world : SourceCompilerWorld.World) (body : LoadedBody) :
    Except String MIR.SpanRef := do
  let actual ← currentBody world body
  let some span := world.canonical.spans[actual.preambleDefSpanId]?
    | throw "current preamble span absent"
  unless span.lo ≤ span.hi && span.file < world.canonical.files.size do
    throw "current preamble span payload invalid"
  return ⟨actual.preambleDefSpanId⟩

def livePreambleSpan (p : Prepared)
    (access : SourceCompilerWorld.Access (MachineHooks.State K User))
    (body : LoadedBody) : MachineHooks.M K User MIR.SpanRef := do
  let world ← currentWorld access
  if world.canonical.sourceMaterial.isNone then return ← preambleSpan p body
  lift (sourcePreambleSpan world body)

def liveRequiredConstants (p : Prepared)
    (access : SourceCompilerWorld.Access (MachineHooks.State K User))
    (body : LoadedBody) : MachineHooks.M K User Unit := do
  let world ← currentWorld access
  if world.canonical.sourceMaterial.isNone then return ← requiredConstants p body
  let actual ← lift (currentBody world body)
  let frame ← MachineHooks.currentFrame
  unless frame.bodyIdentity == body.identity && frame.functionInstance == actual.instanceId do
    throw (.invalidProgram "required-constant current frame identity/instance mismatch")
  for constant in actual.requiredConsts do
    let _ ← SourceCompilerConstantRequests.consume access constant

/-- Legacy delegation is pointwise and still requires the actual World. -/
theorem livePreambleSpan_legacy_at (p : Prepared)
    (access : SourceCompilerWorld.Access (MachineHooks.State K User)) (body : LoadedBody)
    (before : MachineHooks.State K User) (world : SourceCompilerWorld.World)
    (present : access.get before = some world) (legacy : world.canonical.sourceMaterial = none) :
    livePreambleSpan p access body before = preambleSpan p body before := by
  simp [livePreambleSpan, currentWorld, present, legacy,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure]

/-- The legacy constant action retains its exact result and resulting state. -/
theorem liveRequiredConstants_legacy_at (p : Prepared)
    (access : SourceCompilerWorld.Access (MachineHooks.State K User)) (body : LoadedBody)
    (before : MachineHooks.State K User) (world : SourceCompilerWorld.World)
    (present : access.get before = some world) (legacy : world.canonical.sourceMaterial = none) :
    liveRequiredConstants p access body before = requiredConstants p body before := by
  simp [liveRequiredConstants, currentWorld, present, legacy,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure]

/-- Source mode uses live canonical metadata. Legacy schema12 keeps its checked
prepared path and the associated theorems below. -/
def liveHooks (p : Prepared)
    (access : SourceCompilerWorld.Access (MachineHooks.State K User))
    (base : CallMachine.Lifecycle K User C) : CallMachine.Lifecycle K User C :=
  {base with
    preambleSpan := livePreambleSpan p access
    requiredConstants := liveRequiredConstants p access}

def hooks (p : Prepared) (base : CallMachine.Lifecycle K User C) : CallMachine.Lifecycle K User C :=
  {base with preambleSpan := preambleSpan p, requiredConstants := requiredConstants p}
end Miri.Input.CompilerLifecycle

namespace Miri.Input.CompilerLifecycle
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.MIR
set_option autoImplicit false
variable {K U : Type}
theorem preamble_known (p : Prepared) (body : LoadedBody) (actual : LoweredBody)
    (span : SpanRef) (fnInstance : CallInstance)
    (row : p.program.bundle.bodies[body.identity.index]? = some actual)
    (contents : actual.body = body.body)
    (evidence : p.entries[body.identity.index]? = some ⟨.ok span,.ok fnInstance⟩) :
    (preambleSpan p body : MachineHooks.M K U SpanRef) = pure span := by
  simp [preambleSpan, entry, lift, row, contents, evidence,
    bind, Except.bind, pure, Except.pure]
 theorem required_empty (p : Prepared) (body : LoadedBody) (actual : LoweredBody)
    (span : SpanRef) (fnInstance : CallInstance)
    (row : p.program.bundle.bodies[body.identity.index]? = some actual)
    (contents : actual.body = body.body)
    (evidence : p.entries[body.identity.index]? = some ⟨.ok span,.ok fnInstance⟩)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U)
    (identity : frame.bodyIdentity = body.identity)
    (function : frame.functionInstance = fnInstance) :
    requiredConstants p body (⟨⟨frames.push frame⟩,machine⟩ : MachineHooks.State K U) =
      .ok () ⟨⟨frames.push frame⟩,machine⟩ := by
  simp [requiredConstants, entry, lift, row, contents, evidence,
    MachineHooks.currentFrame, Stack.currentFrame?, identity, function,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
    Except.bind,Except.pure]
end Miri.Input.CompilerLifecycle

open Lean Elab Command in
run_cmd do
  for name in #[``Miri.Input.CompilerLifecycle.livePreambleSpan_legacy_at,
      ``Miri.Input.CompilerLifecycle.liveRequiredConstants_legacy_at] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved lifecycle pointwise axiom {dependency} in {name}"
