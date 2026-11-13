import Miri.Input.CompilerProviders
import Miri.Interpreter.ConstantMachine
import Miri.Interpreter.GlobalByteMachine
import Miri.Input.RuntimeArrayQueries
import Miri.Input.WorldIntrinsicTypeName

/-! Direct intrinsics.rs type_name/caller_location ConstValue queries. Source
allocation identities are materialized by the actual constant root-pointer
pipeline, with supplied destination layout checked at the original event. -/
namespace Miri.Input.CompilerValueConstants
open Lean Miri.ABI Miri.Interpreter Miri.Memory
private def checked (p : CompilerProviders.Prepared) (ty : MIR.TyId) (value : MIR.ConstValue) :
    Except String (MIR.TyId × MIR.ConstValue) := do
  let _ ← p.runtime.node ty |>.mapError toString
  pure (ty, value)

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

/-- alloc_type_name reserves immutable CTFE bytes with fixed salt zero before
const_val_to_op checks the supplied layout and adjusts the runtime root. A runtime
AllocId never passes through the exported-graph ConstValue namespace. -/
def typeNameHook (p : CompilerProviders.Prepared) (types : RuntimeArrayQueries.Access (MachineHooks.State K U))
    (functions : FunctionPointers.Hooks K U Other)
    (reserveBytes : Array UInt8 → UInt64 → MachineHooks.M K U AllocId)
    (checkKnown : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (_ : C) (ty : MIR.TyId) (destination : LocalLayout) : MachineHooks.M K U (OpTy Provenance) := do
  let monomorphic ← RuntimeArrayQueries.perform types do
    match WorldTypeFlags.query (← get) "is_monomorphic_enough" (max 256 p.runtime.materialLayoutFuel) ty with
    | .ok value => pure value
    | .error reason => throw reason
  unless monomorphic do throw (.invalidProgram "type_name type still requires instantiation")
  let name ← RuntimeArrayQueries.perform types
    (WorldIntrinsicTypeName.query p.runtime p.runtime.materialLayoutFuel ty)
  let bytes := name.toUTF8.data
  if bytes.size >= 2^64 then throw (.invalidProgram "type_name UTF8 length exceeds source u64")
  let allocation ← reserveBytes bytes 0
  let computed ← RuntimeArrayQueries.layoutOf types destination.ty
  unless ← checkKnown computed destination do
    throw (.invalidProgram "known type_name constant layout differs from compiler layout")
  let pointer ← FunctionPointers.rootPointer functions allocation
  let immediate ← match Immediate.newSlice pointer.withOptionalProvenance
      (UInt64.ofNat bytes.size) p.runtime.target.base with
    | .ok value => pure value
    | .error error => throw (.invalidProgram s!"type_name slice constant: {reprStr error}")
  pure ⟨.immediate immediate,destination⟩

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
