import Miri.Input.CompilerInstance
import Miri.Interpreter.CallMachine
import Miri.Input.RuntimeArrayQueries

/-! The resolved body identifies its concrete callee and preamble span.
Required constants are evaluated before export; frame identity remains checked at entry. -/
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
  for index in [:program.bodyCount] do
    let source := program.bodyMetadata index
    let preamble := do
      let metadata ← source
      lowerCompilerSpan tables ⟨metadata.preambleDefSpanId⟩
    let preamble ← match preamble with
      | .error error => pure (.error error)
      | .ok (span,next) =>
        tables := next
        pure (.ok span)
    let decoded : Except String (CallInstance × CompilerTables) := do
      let metadata ← source
      unless metadata.instanceId < ctx.instances.size do throw "body instance ID out of bounds"
      pure (metadata.instanceId,tables)
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
private def entry (p : Prepared) (body : LoadedBody) (actual : LoweredBody) : Except String Entry := do
  unless actual.body == body.body do throw "canonical body identity/content mismatch"
  let some entry := p.entries[body.identity.index]? | throw "body lifecycle evidence absent"
  return entry

def preambleSpan (p : Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K User))
    (body : LoadedBody) : MachineHooks.M K User MIR.SpanRef := do
  let actual ← RuntimeArrayQueries.perform types (p.program.resolveBody body.identity.index)
  lift do (← entry p body actual).preamble

def requiredConstants (p : Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K User))
    (body : LoadedBody) : MachineHooks.M K User Unit := do
  let actual ← RuntimeArrayQueries.perform types (p.program.resolveBody body.identity.index)
  let entry ← lift (entry p body actual)
  let callee ← lift entry.callee
  let frame ← MachineHooks.currentFrame
  unless frame.bodyIdentity == body.identity && frame.functionInstance == callee do
    throw (.invalidProgram "required-constant current frame identity/instance mismatch")
  pure ()

def hooks (p : Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K User)) (base : CallMachine.Lifecycle K User C) : CallMachine.Lifecycle K User C :=
  {base with preambleSpan := preambleSpan p types, requiredConstants := requiredConstants p types}
end Miri.Input.CompilerLifecycle

namespace Miri.Input.CompilerLifecycle
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.MIR
set_option autoImplicit false
variable {K U : Type}
theorem preamble_known (p : Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K U)) (body : LoadedBody) (actual : LoweredBody)
    (span : SpanRef) (fnInstance : CallInstance)
    (row : (RuntimeArrayQueries.perform types (p.program.resolveBody body.identity.index) : MachineHooks.M K U LoweredBody) = pure actual)
    (contents : actual.body = body.body)
    (evidence : p.entries[body.identity.index]? = some ⟨.ok span,.ok fnInstance⟩) :
    (preambleSpan p types body : MachineHooks.M K U SpanRef) = pure span := by
  funext state
  simp [preambleSpan, entry, lift, row, contents, evidence,
    bind, EStateM.bind, Except.bind, pure, EStateM.pure, Except.pure]
 theorem required_empty (p : Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K U)) (body : LoadedBody) (actual : LoweredBody)
    (span : SpanRef) (fnInstance : CallInstance)
    (row : (RuntimeArrayQueries.perform types (p.program.resolveBody body.identity.index) : MachineHooks.M K U LoweredBody) = pure actual)
    (contents : actual.body = body.body)
    (evidence : p.entries[body.identity.index]? = some ⟨.ok span,.ok fnInstance⟩)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U)
    (identity : frame.bodyIdentity = body.identity)
    (function : frame.functionInstance = fnInstance) :
    requiredConstants p types body (⟨⟨frames.push frame⟩,machine⟩ : MachineHooks.State K U) =
      .ok () ⟨⟨frames.push frame⟩,machine⟩ := by
  simp [requiredConstants, entry, lift, row, contents, evidence,
    MachineHooks.currentFrame, Stack.currentFrame?, identity, function,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
    Except.bind,Except.pure]
end Miri.Input.CompilerLifecycle
