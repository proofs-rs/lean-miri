import Miri.Input.CompilerFacts
import Miri.Input.CompilerInstance
import Miri.Interpreter.OperandMachine

/-! Source intrinsics/mod.rs fallback policy and machine.rs runtime_checks.
Attribute membership and intrinsic override policy are actual rustc queries,
never inferred from a spelling or absence of an implementation in Lean.
-/
namespace Miri.Input.CompilerIntrinsicFacts
open Lean Miri.Interpreter
abbrev Metadata := IntrinsicData
structure Entry where
  callee : CallInstance
  data : RuntimeInstanceData
structure Prepared where
  context : CompilerFacts.Context
  entries : Array Entry
  checks : Array (MIR.RuntimeChecks × Bool)

@[inline] def Prepared.program (prepared : Prepared) : LoweredProgram := prepared.context.program
@[inline] def Prepared.owner (prepared : Prepared) : RuntimeProgram := prepared.context.owner

def Prepared.withProgram (prepared : Prepared) (program : LoweredProgram) : Prepared :=
  {prepared with context := prepared.context.withProgram program}

def prepare (context : CompilerFacts.Context) : Except String Prepared := do
  let program := context.program
  let records ← program.input.mirTables.runtimeInstances
  let mut entries := #[]
  for record in records do
    let callee ← program.input.mirTables.instance record.instanceId
    unless !(entries.any (·.callee == callee)) do throw "duplicate full-instance intrinsic metadata key"
    entries := entries.push ⟨callee,record⟩
  let checks ← (← program.input.mirTables.sessionMetadata).runtimeChecks
  pure ⟨context,entries,checks⟩
private def entry (prepared : Prepared) (callee : CallInstance) : Except String Entry := do
  let some entry := prepared.entries.find? (·.callee == callee)
    | throw "missing exact full-instance intrinsic metadata"
  pure entry

def itemName (prepared : Prepared) (callee : CallInstance) : Except String String := do
  (← entry prepared callee).data.itemName
private def metadata (prepared : Prepared) (callee : CallInstance) : Except String Metadata := do
  let some value ← (← entry prepared callee).data.intrinsic
    | throw "source intrinsic metadata unwrap: definition is not an intrinsic"
  pure value

def mustOverride (prepared : Prepared) (callee : CallInstance) : Except String Bool := do
  pure (← metadata prepared callee).mustOverride

def fallbackIsSpec (prepared : Prepared) (callee : CallInstance) : Except String Bool := do
  pure (← metadata prepared callee).fallbackIsSpec

def runtimeChecks (prepared : Prepared) (kind : MIR.RuntimeChecks) : Except String Bool := do
  let some (_,enabled) := prepared.checks.find? (·.1 == kind)
    | throw "missing actual compiler session runtime-check value"
  pure enabled

def operandHooks (prepared : Prepared) (base : OperandMachine.Hooks K User C) :
    OperandMachine.Hooks K User C :=
  { base with runtimeChecks := fun _ kind =>
      match runtimeChecks prepared kind with
      | .ok enabled => pure enabled
      | .error reason => throw (.unsupported reason) }
end Miri.Input.CompilerIntrinsicFacts
