import Miri.Input.CompilerConstantQueries
import Miri.Interpreter.CallMachine

/-! Exact body-keyed compiler results for the source stack preamble. Failed
normalization/evaluation is retained until the corresponding runtime event. -/
namespace Miri.Input.CompilerLifecycle
open Lean Miri.Interpreter
structure Entry where
  preamble : Except String MIR.SpanRef
  callee : Except String CallInstance
  checks : Except String (Array (Except StepError CompilerConstantEvidence))
structure Prepared where
  program : LoweredProgram
  entries : Array Entry

private def supported (j : Json) : Except String Unit := do
  unless (← (← j.getObjVal? "status").getStr?) == "supported" do
    throw s!"unresolved compiler lifecycle query: {j.compress}"

private def decodeChecks (ctx : LowerContext) (interner : CompilerSpanInterner)
    (callee : CallInstance) (payload : Json) :
    Except String (Array (Except StepError CompilerConstantEvidence) × CompilerSpanInterner) := do
  let original ← (← payload.getObjVal? "required_consts").getArr?
  let query ← (← payload.getObjVal? "constant_query_context").getObjVal? "required_constant_checks"
  supported query
  unless (← (← query.getObjVal? "typing_env").getStr?) == "body_typing_env" do
    throw "required-constant typing environment mismatch"
  let checks ← (← query.getObjVal? "checks").getArr?
  unless checks.size == original.size do throw "required-constant query count mismatch"
  let mut interner := interner
  let mut evidence := #[]
  for index in [:checks.size] do
    let some check := checks[index]? | throw "required check absent"
    let some source := original[index]? | throw "required source operand absent"
    unless (← (← check.getObjVal? "index").getNat?) == index do throw "required-constant source order mismatch"
    unless (← check.getObjVal? "span") == (← source.getObjVal? "span") do
      throw "required-constant source span mismatch"
    let result ← check.getObjVal? "result"
    if ((result.getObjVal? "status").bind Json.getStr?).toOption == some "supported" then
      let normalized ← result.getObjVal? "normalized_operand"
      unless (← normalized.getObjVal? "span") == (← source.getObjVal? "span") do
        throw "required constant normalization changed source span"
      let (source,nextInterner) ← lowerCompilerConstOperandWithInterner ctx interner (← decodeCompilerValue source)
      let (normal,nextInterner) ← lowerCompilerConstOperandWithInterner ctx nextInterner (← decodeCompilerValue normalized)
      let ty ← (← normalized.getObjVal? "type").getObjValAs? Nat "type_id"
      let value ← lowerCompilerConstValue ctx ty (← decodeCompilerValue (← result.getObjVal? "value"))
      interner := nextInterner
      evidence := evidence.push (.ok ⟨callee,source.value,normal.value,normal.span,value⟩)
    else
      let kind := ((result.getObjVal? "kind").bind Json.getStr?).toOption
      let error := if kind == some "required_const_normalization_error" ||
          kind == some "required_const_evaluation_error" then
        StepError.invalidProgram s!"required constant compiler failure: {result.compress}"
        else StepError.unsupported s!"required constant unresolved: {result.compress}"
      evidence := evidence.push (.error error)
  return (evidence,interner)

def prepare (program : LoweredProgram) : Prepared := Id.run do
  let ctx := LowerContext.ofDocument program.input
  let mut interner := CompilerSpanInterner.ofTables program.compilerTables
  let mut entries := #[]
  for body in program.bundle.bodies do
    let preamble := do
      lowerCompilerSpanWithInterner interner (← decodeCompilerValue (← body.input.payload.getObjVal? "preamble_def_span"))
    let preamble ← match preamble with
      | .error error => pure (.error error)
      | .ok (span,next) =>
        interner := next
        pure (.ok span)
    let decoded := do
      CompilerInstance.decode ctx interner.getTables (← body.input.payload.getObjVal? "constant_query_context")
    let callee ← match decoded with
      | .error error => pure (.error error)
      | .ok (callee,next) =>
        interner := interner.rebind next
        pure (.ok callee)
    let checks := do decodeChecks ctx interner (← callee) body.input.payload
    let checks ← match checks with
      | .error error => pure (.error error)
      | .ok (checks,next) =>
        interner := next
        pure (.ok checks)
    entries := entries.push ⟨preamble,callee,checks⟩
  return ⟨program.withCompilerTables interner.getTables,entries⟩

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
