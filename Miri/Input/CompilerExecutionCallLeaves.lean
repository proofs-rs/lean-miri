import Miri.Input.CompilerProviders
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

/-- Exact source ExternAbi identity, canonical FnAbi records, shared DefIds/
TypeConstIds and actual current BodyIdentity all belong to this same program. -/
def make (p : CompilerProviders.Prepared) (compatibilityBudget : Nat) :
    ExecutionCallLeaves.Compiler (MachineHooks.State K U) C ABI.ExternAbi := {
  functionSignature := fun _ layout => lift do
    let (count,sourceAbi) ← CompilerFunctionFacts.signature p.functions layout.ty
    pure (count, sourceAbi)
  instanceKind := fun inst => lift (CompilerInstance.kindOf p.loweringContext p.program.compilerTables inst)
  instanceArgs := fun inst => lift (CompilerInstance.argsOf p.loweringContext p.program.compilerTables inst)
  itemInstance := fun definition args => lift (CompilerInstance.item p.loweringContext p.program.compilerTables definition args)
  functionKind := fun ty => lift (CompilerFunctionFacts.kind p.functions ty)
  resolve := fun _ definition args => CompilerProviders.resolveCurrent p definition args
  fnAbiOfFnPtr := fun _ layout extra => lift (CompilerFunctionFacts.pointerAbi p.functions layout.ty extra)
  fnAbiOfInstance := fun _ callee extra => lift (CompilerInstanceAbi.abiOfInstance p.lifecycle.instances callee extra)
  isRustCall := fun abi => abi == .RustCall
  rustAbi := .Rust
  checkArgumentCompat := fun _ caller callee =>
    LayoutCompat.checkArgumentCompat (CompilerFacts.compatibilityQueries p.lifecycle.calls.symbols.facts.context)
      compatibilityBudget caller callee
  targetFeatures := CompilerTargetFeatures.dictionary p.intrinsics
  tupleFields := fun ty => lift (tupleFields p ty)
  isClosureLike := fun callee => lift (CompilerCallFacts.isClosureLike p.intrinsics callee)
  closureUpvarCount := fun ty => lift (closureUpvarCount p ty)
  llvmLinkName := fun callee => do
    let some name ← lift (CompilerCallFacts.codegenSymbolName p.intrinsics callee)
      | throw (.invalidProgram "source LLVM intrinsic requires a codegen symbol_name attribute")
    pure name }
end Miri.Input.CompilerExecutionCallLeaves
