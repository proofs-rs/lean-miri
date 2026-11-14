import Miri.Input.CompilerInstance
import Miri.Input.LowerMIR
import Miri.Interpreter.OperandMachine

/-! Source intrinsics/mod.rs fallback policy and machine.rs runtime_checks.
Attribute membership and intrinsic override policy are actual rustc queries,
never inferred from a spelling or absence of an implementation in Lean.
-/
namespace Miri.Input.CompilerIntrinsicFacts
open Lean Miri.Interpreter
structure Metadata where
  mustOverride : Bool
  fallbackIsSpec : Bool
structure Entry where
  callee : CallInstance
  name : Except String String
  intrinsic : Except String (Option Metadata)
  facts : Catalog.RuntimeInstance
structure Prepared where
  program : LoweredProgram
  entries : Array Entry
  checks : Array (MIR.RuntimeChecks × Bool)
def prepare (program : LoweredProgram) : Except String Prepared := do
  let ctx := LowerContext.ofDocument program.input
  let mut entries := #[]
  for record in program.input.queries.runtime.instances do
    let callee := record.instanceId
    let _ ← CompilerInstance.Material.source ctx.instances callee
    unless !(entries.any (·.callee == callee)) do throw "duplicate full-instance intrinsic metadata key"
    let name := match record.itemName with | some value => .ok value | none => .error "compiler item name absent"
    let intrinsic := do
      let some query := record.intrinsicMetadata | throw "compiler intrinsic metadata query absent"
      pure (query.map fun value => (⟨value.mustOverride, value.fallbackIsSpec⟩ : Metadata))
    entries := entries.push ⟨callee, name, intrinsic, record⟩
  let mut checks := #[]
  for (kind, enabled) in program.input.queries.session.runtimeChecks do
    unless !(checks.any (·.1 == kind)) do throw "duplicate compiler runtime-check query"
    checks := checks.push (kind, enabled)
  pure ⟨program, entries, checks⟩
private def entry (prepared : Prepared) (callee : CallInstance) : Except String Entry := do
  let some entry := prepared.entries.find? (·.callee == callee)
    | throw "missing exact full-instance intrinsic metadata"
  pure entry

def itemName (prepared : Prepared) (callee : CallInstance) : Except String String := do
  (← entry prepared callee).name
private def metadata (prepared : Prepared) (callee : CallInstance) : Except String Metadata := do
  let some value ← (← entry prepared callee).intrinsic
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
