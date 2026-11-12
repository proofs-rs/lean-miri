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

def prepare (program : LoweredProgram) : Prepared := ⟨program⟩

private def lift (query : Except String A) : MachineHooks.M K User A :=
  match query with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler lifecycle: {error}")
def bodyEntry (p : Prepared) (body : LoadedBody) (actual : LoweredBody) : Except String Entry := do
  unless actual.body == body.body do throw "canonical body identity/content mismatch"
  unless actual.input.preambleDefSpanId < p.program.compilerTables.spans.size do
    throw "body preamble span is absent"
  pure ⟨.ok ⟨actual.input.preambleDefSpanId⟩,.ok actual.input.instanceId⟩

def preambleSpan (p : Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K User))
    (body : LoadedBody) : MachineHooks.M K User MIR.SpanRef := do
  let actual ← RuntimeArrayQueries.performCompiler types (p.program.resolveBodyIdentity body.identity)
  lift do (← bodyEntry p body actual).preamble

def requiredConstants (p : Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K User))
    (body : LoadedBody) : MachineHooks.M K User Unit := do
  let actual ← RuntimeArrayQueries.performCompiler types (p.program.resolveBodyIdentity body.identity)
  let entry ← lift (bodyEntry p body actual)
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
    (row : (RuntimeArrayQueries.performCompiler types (p.program.resolveBodyIdentity body.identity) : MachineHooks.M K U LoweredBody) = pure actual)
    (contents : actual.body = body.body)
    (bounded : actual.input.preambleDefSpanId < p.program.compilerTables.spans.size)
    (spanId : actual.input.preambleDefSpanId = span.id)
    (callee : actual.input.instanceId = fnInstance) :
    (preambleSpan p types body : MachineHooks.M K U SpanRef) = pure span := by
  have boundedSpan : span.id < p.program.compilerTables.spans.size := spanId ▸ bounded
  cases span
  funext state
  simp [preambleSpan, bodyEntry, lift, row, contents, boundedSpan, spanId, callee,
    bind, EStateM.bind, Except.bind, pure, EStateM.pure, Except.pure]
 theorem required_empty (p : Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K U)) (body : LoadedBody) (actual : LoweredBody)
    (span : SpanRef) (fnInstance : CallInstance)
    (row : (RuntimeArrayQueries.performCompiler types (p.program.resolveBodyIdentity body.identity) : MachineHooks.M K U LoweredBody) = pure actual)
    (contents : actual.body = body.body)
    (bounded : actual.input.preambleDefSpanId < p.program.compilerTables.spans.size)
    (spanId : actual.input.preambleDefSpanId = span.id)
    (callee : actual.input.instanceId = fnInstance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U)
    (identity : frame.bodyIdentity = body.identity)
    (function : frame.functionInstance = fnInstance) :
    requiredConstants p types body (⟨⟨frames.push frame⟩,machine⟩ : MachineHooks.State K U) =
      .ok () ⟨⟨frames.push frame⟩,machine⟩ := by
  have boundedSpan : span.id < p.program.compilerTables.spans.size := spanId ▸ bounded
  cases span
  simp [requiredConstants, bodyEntry, lift, row, contents, boundedSpan, spanId, callee,
    MachineHooks.currentFrame, Stack.currentFrame?, identity, function,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
    Except.bind,Except.pure]
end Miri.Input.CompilerLifecycle
