import Miri.Input.CompilerColdU64Source
import Miri.Input.RuntimeArrayQueries
import Miri.Interpreter.ExecutionMachine
import Miri.Interpreter.ValidityMachine

/-! Role-specific leaves for the SAME fixed Step interpreter. Runtime MIR
loaders stay strict. Only this exact registered CTFE source key is accepted. -/
namespace Miri.Input.CompilerColdU64Machine
open Miri.Memory Miri.ABI Miri.Interpreter
set_option autoImplicit false
variable {K U C O X Host A : Type}
private def lift (value : Except String A) : MachineHooks.M K U A :=
  match value with | .ok value => pure value | .error error => throw (.unsupported error)
def verify (source : CompilerColdU64Source.Registered)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K U)) : MachineHooks.M K U Unit := do
  lift (CompilerColdU64Source.verify source (types.get (← get)))
private def frame (source : CompilerColdU64Source.Registered)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K U)) : MachineHooks.M K U Unit := do
  verify source types
  let frame ← MachineHooks.currentFrame
  unless frame.bodyIdentity == source.body.identity && frame.body == source.body.body && frame.functionInstance == source.callee do
    throw (.invalidProgram "CTFE active source frame/callee mismatch")

def specialize [DecidableEq K] (source : CompilerColdU64Source.Registered)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K (ValidityMachine.UserState U)))
    (runtime : RuntimeMetadata)
    (base : ExecutionMachine.Config K (ValidityMachine.UserState U) C O X Host) :
    ExecutionMachine.Config K (ValidityMachine.UserState U) C O X Host := Id.run do
  let localLayout := fun (id : Miri.MIR.LocalId) => do
    frame source types
    let some type := source.body.body.locals[id]? | throw (.invalidProgram "CTFE local absent")
    RuntimeArrayQueries.perform types (RuntimeMetadata.layoutInWorld runtime type)
  let compiler := {base.compiler with
    layout := fun _ id => localLayout id
    localSpan := fun supplied id => do
      frame source types
      unless supplied == source.body.body do throw (.invalidProgram "CTFE local span body mismatch")
      let some location := source.source.localSources[id]? | throw (.invalidProgram "CTFE local source span absent")
      pure ⟨location.spanId⟩}
  let lifecycle := {base.lifecycle with
    compiler := {base.lifecycle.compiler with
      requiresCallerLocation := fun callee => do
        verify source types
        unless callee == source.callee do throw (.unsupported "non-root CTFE frame metadata")
        -- Raw Const/AssocConst kind is checked by the loader; track_caller
        -- belongs to function source, with no FnAbi query for this root.
        pure false
      isLocalDefinition := fun callee => do
        verify source types
        unless callee == source.callee do throw (.unsupported "non-root CTFE definition")
        pure (source.definition.crateIndex == 0)
      definitionCrate := fun callee => do
        verify source types
        unless callee == source.callee do throw (.unsupported "non-root CTFE crate")
        pure source.definition.crateIndex
      sourceScope := fun identity callee body scope => do
        frame source types
        unless identity == source.body.identity && callee == source.callee && body == source.body.body do
          throw (.invalidProgram "CTFE source scope context mismatch")
        let some value := source.source.sourceScopes[scope]? | throw (.invalidProgram "CTFE scope absent")
        unless value.inlined.isNone do throw (.unsupported "CTFE inlined scope outside u64 leaf policy")
        pure ⟨none,value.inlinedParent⟩}
    storage := {base.lifecycle.storage with layout := localLayout}
    preambleSpan := fun body => do
      verify source types
      unless body == source.body do throw (.invalidProgram "CTFE preamble key mismatch")
      pure ⟨source.source.preambleDefSpanId⟩
    requiredConstants := fun body => do
      frame source types
      unless body == source.body && source.source.requiredConsts.isEmpty do
        throw (.unsupported "CTFE required constants outside u64 leaf source policy")}
  let projection := {base.projection with place := ValidityMachine.placeHooks base.access base.allocation compiler}
  return {base with compiler,lifecycle,projection,control := ⟨fun value => do
    unless value.bodyIdentity == source.body.identity && value.body == source.body.body do
      throw (.invalidProgram "CTFE body span context mismatch")
    pure ⟨source.source.spanId⟩⟩}

/-- CompileTimeMachine inherits Machine::before_terminator's empty source rule
(interpret/machine.rs360), without Miri scheduler effects. Counter markers are
rejected by the checked u64 leaf policy, never handled by an empty Miri hook. -/
def step [DecidableEq K] (source : CompilerColdU64Source.Registered)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K (ValidityMachine.UserState U)))
    (config : ExecutionMachine.Config K (ValidityMachine.UserState U) C O X Host)
    (limits : ExecutionMachine.Limits) (choice : C) (state : MachineHooks.State K (ValidityMachine.UserState U)) :
    StepResult (MachineHooks.State K (ValidityMachine.UserState U)) Bool :=
  let hooks := {ExecutionMachine.stepHooks config limits with
    beforeTerminator := fun _ state => (state,.ok ())
    incrementConstEvalCounter := fun _ state => (state,.error (.unsupported "CTFE counter marker outside u64 leaf policy"))}
  match state.stack.currentFrame? with
  | none => Step.step hooks choice state
  | some _ =>
    let (state,checked) := MachineHooks.run (frame source types) state
    match checked with
    | .error error => (state,.error error)
    | .ok () => Step.step hooks choice state
end Miri.Input.CompilerColdU64Machine
