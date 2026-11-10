import Miri.Input.CompilerProviders
import Miri.Interpreter.ConstantMachine

/-! Direct intrinsics.rs type_name/caller_location ConstValue queries. Source
allocation identities are materialized by the actual constant root-pointer
pipeline, with supplied destination layout checked at the original event. -/
namespace Miri.Input.CompilerValueConstants
open Lean Miri.ABI Miri.Interpreter Miri.Memory
private def checked (p : CompilerProviders.Prepared) (ty : MIR.TyId) (value : MIR.ConstValue) :
    Except String (MIR.TyId × MIR.ConstValue) := do
  let _ ← p.runtime.node ty |>.mapError toString
  pure (ty, value)

def typeName (p : CompilerProviders.Prepared) (ty : MIR.TyId) :
    Except String (MIR.TyId × MIR.ConstValue) := do
  let matching := p.program.input.queries.typeNames.filter (·.inputType == ty)
  let some first := matching[0]? | throw "missing exact compiler intrinsic constant query"
  unless matching.all (· == first) do throw "conflicting exact compiler intrinsic constant queries"
  checked p first.resultType first.value

def callerLocation (p : CompilerProviders.Prepared) (span : MIR.SpanRef) :
    Except String (MIR.TyId × MIR.ConstValue) := do
  unless span.id < p.program.compilerTables.spans.size do throw "caller-location span absent from shared table"
  let matching := p.program.input.queries.callerLocations.filter (·.span == span.id)
  let some first := matching[0]? | throw "missing exact compiler intrinsic constant query"
  unless matching.all (· == first) do throw "conflicting exact compiler intrinsic constant queries"
  let some ty := first.resultType | throw "compiler caller-location result type absent"
  checked p ty first.value

def callerLocationReference (p : CompilerProviders.Prepared) (span : MIR.SpanRef) :
    Except String (MIR.TyId × MIR.ConstValue) := callerLocation p span

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
