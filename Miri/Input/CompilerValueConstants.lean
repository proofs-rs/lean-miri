import Miri.Input.CompilerProviders
import Miri.Interpreter.ConstantMachine

/-! Direct intrinsics.rs type_name/caller_location ConstValue queries. Source
allocation identities are materialized by the actual constant root-pointer
pipeline, with supplied destination layout checked at the original event. -/
namespace Miri.Input.CompilerValueConstants
open Lean Miri.ABI Miri.Interpreter Miri.Memory
private def unique {α : Type} (entries : Array (Nat × α)) : Except String α := do
  let some (key,first) := entries[0]? | throw "missing exact compiler intrinsic constant query"
  unless entries.all (·.1 == key) do throw "conflicting exact compiler intrinsic constant queries"
  return first

def typeName (p : CompilerProviders.Prepared) (ty : MIR.TyId) :
    Except String (MIR.TyId × MIR.ConstValue) := do
  let matching := (← p.program.input.mirTables.typeNameConstants).filter (·.inputType == some ty)
  unique (matching.map fun entry => (entry.sourceKey,entry.result)) |>.bind id

/-- Span matching compares complete typed source spans against the current
canonical table. Query rows never append spans; malformed rows retain order. -/
def callerLocation (p : CompilerProviders.Prepared) (span : MIR.SpanRef) :
    Except String (MIR.TyId × MIR.ConstValue) := do
  let some target := p.program.compilerTables.spans[span.id]? | throw "caller-location span absent from shared table"
  let mut matching := #[]
  for entry in ← p.program.input.mirTables.callerLocationConstants do
    if (← entry.span) == target then matching := matching.push (entry.sourceKey,entry.result)
  unique matching |>.bind id

def eval (p : CompilerProviders.Prepared)
    (functions : FunctionPointers.Hooks K U Other) (arithmetic : PointerArithmetic)
    (externStatic : MIR.DefId → MachineHooks.M K U (Pointer Provenance))
    (classifyError : ConstantError → StepError)
    (checkKnown : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (query : Except String (MIR.TyId × MIR.ConstValue)) (destination : LocalLayout) :
    MachineHooks.M K U (OpTy Provenance) := do
  let (ty,value) ← match query with
    | .ok value => pure value
    | .error reason => throw (.unsupported reason)
  ConstantMachine.evalValueWithLayout p.runtime functions arithmetic externStatic classifyError
    value ty (some destination) (some checkKnown)

def typeNameHook (p : CompilerProviders.Prepared)
    (functions : FunctionPointers.Hooks K U Other) (arithmetic : PointerArithmetic)
    (externStatic : MIR.DefId → MachineHooks.M K U (Pointer Provenance))
    (classifyError : ConstantError → StepError)
    (checkKnown : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (_ : C) (ty : MIR.TyId) (destination : LocalLayout) : MachineHooks.M K U (OpTy Provenance) :=
  eval p functions arithmetic externStatic classifyError checkKnown (typeName p ty) destination

def callerLocationHook (p : CompilerProviders.Prepared)
    (functions : FunctionPointers.Hooks K U Other) (arithmetic : PointerArithmetic)
    (externStatic : MIR.DefId → MachineHooks.M K U (Pointer Provenance))
    (classifyError : ConstantError → StepError)
    (checkKnown : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (currentLocation : MachineHooks.M K U MIR.SpanRef)
    (_ : C) (destination : LocalLayout) : MachineHooks.M K U (OpTy Provenance) := do
  let span ← currentLocation
  eval p functions arithmetic externStatic classifyError checkKnown (callerLocation p span) destination
end Miri.Input.CompilerValueConstants
