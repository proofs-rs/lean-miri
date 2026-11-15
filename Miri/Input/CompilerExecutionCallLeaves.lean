import Miri.Input.SourceCompilerWorldAbi
import Miri.Input.CompilerProviders
import Miri.Input.SourceCompilerInstances
import Miri.Input.SourceCallFacts
import Miri.Input.CompilerCallFacts
import Miri.Input.CompilerTargetFeatures
import Miri.Interpreter.ExecutionCallLeaves

/-! Construct the complete source call compiler dictionary from the single
prepared compiler program. No independently supplied signature/ABI/type/target
feature dictionary is accepted. Source query failures remain typed errors at
that operation; no names or equivalent layouts establish identities. -/
namespace Miri.Input.CompilerExecutionCallLeaves
open Lean Miri.ABI Miri.Interpreter
private def lift (query : Except String A) : MachineHooks.M K U A :=
  match query with | .ok value => pure value | .error error => throw (.unsupported error)

private def source (access : SourceCompilerWorld.Access (MachineHooks.State K U))
    (query : SourceCompilerWorld.World → Except String A) : MachineHooks.M K U A := do
  let some world := access.get (← get) | throw (.unsupported "source call-facts World unavailable")
  unless world.canonical.sourceMaterial.isSome do throw (.unsupported "source call-facts material unavailable")
  lift (query world)

def tupleFields (p : CompilerProviders.Prepared) (ty : MIR.TyId) : Except String (Array MIR.TyId) := do
  let node ← p.runtime.node ty |>.mapError toString
  unless node.shapeKind == .tuple do
    throw "source RustCall spreading requires the exact tuple type"
  let .tuple elements := node.shape | throw "tuple field query on non-tuple"
  for id in elements do
    let _ ← p.runtime.node id |>.mapError toString
  pure elements

def closureUpvarCount (p : CompilerProviders.Prepared) (ty : MIR.TyId) : Except String (Option Nat) := do
  let node ← p.runtime.node ty |>.mapError toString
  match node.shape with
  | .closure _ _ count => pure (some count)
  | _ => pure none

/-- Canonical shapes have already passed interning validation. Tuple children
and closure capture counts retain their actual type-pool identities. -/
def tupleFieldsSource (world : SourceCompilerWorld.World) (ty : MIR.TyId) : Except String (Array MIR.TyId) := do
  let some node := world.canonical.types[ty]? | throw "source RustCall tuple type unavailable"
  let .tuple fields := node.shape | throw "source RustCall spreading requires the exact tuple type"
  return fields

def closureUpvarCountSource (world : SourceCompilerWorld.World) (ty : MIR.TyId) : Except String (Option Nat) := do
  let some node := world.canonical.types[ty]? | throw "source closure argument type unavailable"
  match node.shape with
  | .closure _ _ count => pure (some count)
  | _ => pure none

/-- Exact source ExternAbi identity, canonical FnAbi records, shared DefIds/
TypeConstIds and actual current BodyIdentity all belong to this same program. -/
def make (p : CompilerProviders.Prepared) (compatibilityBudget : Nat)
    (world : SourceCompilerWorld.Access (MachineHooks.State K U)) :
    ExecutionCallLeaves.Compiler (MachineHooks.State K U) C ABI.ExternAbi := {
  functionSignature := fun _ layout => SourceCompilerWorld.demandFunctionSignature world layout.ty
  instanceKind := SourceCompilerInstances.instanceKind world
  instanceArgs := SourceCompilerInstances.instanceArgs world
  itemInstance := SourceCompilerInstances.itemInstance world
  functionKind := SourceCompilerInstances.functionKind world
  resolve := fun _ definition args => CompilerProviders.resolveCurrent world definition args
  fnAbiOfFnPtr := fun _ layout extra => SourceCompilerWorld.demandFunctionPointerAbi world layout.ty extra
  fnAbiOfInstance := fun _ callee extra => SourceCompilerWorld.demandInstanceAbi world callee extra
  isRustCall := fun abi => abi == .RustCall
  rustAbi := .Rust
  checkArgumentCompat := fun _ caller callee =>
    LayoutCompat.checkArgumentCompat (CompilerFacts.compatibilityQueries p.lifecycle.calls.symbols.facts.context)
      compatibilityBudget caller callee
  targetFeatures := CompilerTargetFeatures.dictionary p.intrinsics world
  tupleFields := fun ty => if p.runtime.source.sourceMaterial.isSome then
    source world (tupleFieldsSource · ty)
    else lift (tupleFields p ty)
  isClosureLike := fun callee => if p.runtime.source.sourceMaterial.isSome then
    source world (SourceCallFacts.isClosureLike · callee)
    else lift (CompilerCallFacts.isClosureLike p.intrinsics callee)
  closureUpvarCount := fun ty => if p.runtime.source.sourceMaterial.isSome then
    source world (closureUpvarCountSource · ty)
    else lift (closureUpvarCount p ty)
  llvmLinkName := fun callee => do
    let name ← if p.runtime.source.sourceMaterial.isSome then
      source world (SourceCallFacts.codegenSymbolName · callee)
      else lift (CompilerCallFacts.codegenSymbolName p.intrinsics callee)
    let some name := name
      | throw (.invalidProgram "source LLVM intrinsic requires a codegen symbol_name attribute")
    pure name }
/-- Exact closure-kind query boundary over the current compiler World. -/
theorem isClosureLike_at {C : Type} (p : CompilerProviders.Prepared) (budget : Nat)
    (access : SourceCompilerWorld.Access (MachineHooks.State K U))
    (callee : CallInstance) (before : MachineHooks.State K U) :
    (make (C := C) p budget access).isClosureLike callee before =
      if p.runtime.source.sourceMaterial.isSome then
        match access.get before with
        | none => .error (.unsupported "source call-facts World unavailable") before
        | some world =>
          if world.canonical.sourceMaterial.isSome then match SourceCallFacts.isClosureLike world callee with
            | .ok value => .ok value before
            | .error reason => .error (.unsupported reason) before
          else .error (.unsupported "source call-facts material unavailable") before
      else match CompilerCallFacts.isClosureLike p.intrinsics callee with
        | .ok value => .ok value before
        | .error reason => .error (.unsupported reason) before := by
  cases mode : p.runtime.source.sourceMaterial.isSome with
  | false =>
    cases result : CompilerCallFacts.isClosureLike p.intrinsics callee <;>
      simp [make, mode, lift, result, pure, EStateM.pure] <;> rfl
  | true =>
    cases current : access.get before with
    | none =>
      simp [make, mode, source, current, get, getThe, MonadStateOf.get,
        EStateM.get, bind, EStateM.bind, pure, EStateM.pure] <;> rfl
    | some world =>
      cases material : world.canonical.sourceMaterial.isSome with
      | false =>
        simp [make, mode, source, current, material, get, getThe, MonadStateOf.get,
          EStateM.get, bind, EStateM.bind, pure, EStateM.pure] <;> rfl
      | true =>
        cases result : SourceCallFacts.isClosureLike world callee <;>
          simp [make, mode, source, lift, current, material, result,
            get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure] <;> rfl

end Miri.Input.CompilerExecutionCallLeaves
