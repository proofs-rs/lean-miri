import Miri.Input.CompilerConstantQueries
import Miri.Interpreter.CallMachine

/-! Exact body-keyed compiler results for the source stack preamble.
Malformed or missing metadata remains an error at the corresponding runtime event. -/
namespace Miri.Input.CompilerLifecycle
open Lean Miri.Interpreter
structure Entry where
  preamble : Except String MIR.SpanRef
  callee : Except String CallInstance
  checks : Except String (Array (Except StepError CompilerConstantEvidence))
structure Prepared where
  program : LoweredProgram
  entries : Array Entry

private def decodeChecks (ctx : LowerContext) (tables : CompilerTables)
    (callee : CallInstance) (body : BodyCore) :
    Except String (Array (Except StepError CompilerConstantEvidence) × CompilerTables) := do
  let some original := body.requiredConsts | throw "required source constants are absent"
  let some query := body.constantQueryContext | throw "constant query context is absent"
  unless query.requiredTypingEnvironment == "body_typing_env" do
    throw "required-constant typing environment mismatch"
  let checks := query.requiredChecks
  unless checks.size == original.size do throw "required-constant query count mismatch"
  let mut tables := tables
  let mut evidence := #[]
  for index in [:checks.size] do
    let some check := checks[index]? | throw "required check absent"
    let some source := original[index]? | throw "required source operand absent"
    unless check.index == index do throw "required-constant source order mismatch"
    let sourceSpan ← (← source.field "span").natural
    unless check.spanId == sourceSpan do throw "required-constant source span mismatch"
    let normalized := check.normalizedOperand
    unless (← (← normalized.field "span").natural) == sourceSpan do
      throw "required constant normalization changed source span"
    let (source,nextTables) ← lowerCompilerConstOperand ctx tables source
    let (normal,nextTables) ← lowerCompilerConstOperand ctx nextTables normalized
    let ty ← (← normalized.field "type").natural
    let value ← lowerCompilerConstValue ctx ty check.value
    tables := nextTables
    evidence := evidence.push (.ok ⟨callee,source.value,normal.value,normal.span,value⟩)
  return (evidence,tables)

def prepare (program : LoweredProgram) : Prepared := Id.run do
  let ctx := LowerContext.ofDocument program.input
  let mut tables := program.compilerTables
  let mut entries := #[]
  let executable := program.executableBodyIds
  for (body, bodyIndex) in program.bundle.bodies.toList.zipIdx do
    unless executable.contains bodyIndex do
      let unavailable := "body is compiler-query metadata, not an executable body"
      entries := entries.push ⟨.error unavailable, .error unavailable, .error unavailable⟩
      continue
    let preamble := do
      lowerCompilerSpan tables (.sourceSpan body.input.preambleDefSpanId)
    let preamble ← match preamble with
      | .error error => pure (.error error)
      | .ok (span,next) =>
        tables := next
        pure (.ok span)
    let decoded : Except String (CallInstance × CompilerTables) := do
      let some query := body.input.constantQueryContext | throw "constant query context is absent"
      unless query.instanceId < ctx.instances.size do throw "constant query instance ID out of bounds"
      pure (query.instanceId,tables)
    let callee ← match decoded with
      | .error error => pure (.error error)
      | .ok (callee,next) =>
        tables := next
        pure (.ok callee)
    let checks := do decodeChecks ctx tables (← callee) body.input
    let checks ← match checks with
      | .error error => pure (.error error)
      | .ok (checks,next) =>
        tables := next
        pure (.ok checks)
    entries := entries.push ⟨preamble,callee,checks⟩
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
  for check in ← lift entry.checks do
    match check with
    | .ok _ => pure ()
    | .error error => throw error

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
    (evidence : p.entries[body.identity.index]? = some ⟨.ok span,.ok fnInstance,.ok #[]⟩) :
    (preambleSpan p body : MachineHooks.M K U SpanRef) = pure span := by
  simp [preambleSpan, entry, lift, row, contents, evidence,
    bind, Except.bind, pure, Except.pure]
 theorem required_empty (p : Prepared) (body : LoadedBody) (actual : LoweredBody)
    (span : SpanRef) (fnInstance : CallInstance)
    (row : p.program.bundle.bodies[body.identity.index]? = some actual)
    (contents : actual.body = body.body)
    (evidence : p.entries[body.identity.index]? = some ⟨.ok span,.ok fnInstance,.ok #[]⟩)
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
