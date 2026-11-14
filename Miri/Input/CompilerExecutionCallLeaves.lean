import Miri.Input.CompilerProviders
import Miri.Input.CompilerWorldCompatibility
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

/-- Exact source ExternAbi identity, canonical FnAbi records, shared DefIds/
TypeConstIds and actual current BodyIdentity all belong to this same program. -/
def make (p : CompilerProviders.Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K U)) (compatibilityBudget : Nat)
    (typeConstants : RuntimeEffectfulLayout.Provider (MachineHooks.State K U) := RuntimeEffectfulLayout.unavailable) :
    ExecutionCallLeaves.Compiler (MachineHooks.State K U) C ABI.ExternAbi := {
  functionSignature := fun _ layout => RuntimeArrayQueries.performCompiler types
    (CompilerFunctionFacts.signatureInWorld p.functions layout.ty)
  instanceKind := fun inst => do lift (CompilerInstance.kindOf (← RuntimeArrayQueries.compilerSnapshot types) inst)
  instanceArgs := fun inst => do lift (CompilerInstance.argsOf (← RuntimeArrayQueries.compilerSnapshot types) inst)
  itemInstance := fun definition args => lift
    (CompilerInstance.Material.item p.program.input.instances definition args)
  functionKind := fun ty => RuntimeArrayQueries.perform types (CompilerFunctionFacts.kindInWorld p.functions ty)
  resolve := fun _ definition args => CompilerProviders.resolveCurrent p types definition args
  fnAbiOfFnPtr := fun _ layout extra => RuntimeArrayQueries.performCompiler types
      (CompilerFunctionFacts.pointerAbiInWorld p.functions layout.ty extra)
  fnAbiOfInstance := fun _ callee extra => RuntimeArrayQueries.performCompiler types
    (CompilerInstanceAbi.abiOfInstanceInWorld p.lifecycle.instances callee extra)
  isRustCall := fun abi => abi == .RustCall
  rustAbi := .Rust
  checkArgumentCompat := fun _ caller callee =>
    LayoutCompat.checkArgumentCompat (CompilerWorldCompatibility.queries p.lifecycle.calls.symbols.facts.context types typeConstants)
      compatibilityBudget caller callee
  targetFeatures := CompilerTargetFeatures.dictionary p.intrinsics
  tupleFields := fun ty => do
    let .tuple fields ← RuntimeArrayQueries.perform types
      (CompilerFactAdapters.castTypeInfoInWorld p.lifecycle.calls.symbols.facts ty)
      | throw (.unsupported "source RustCall spreading requires the exact tuple type")
    pure fields
  isClosureLike := fun callee => lift (CompilerCallFacts.isClosureLike p.intrinsics callee)
  closureUpvarCount := fun ty => do
    let kind ← RuntimeArrayQueries.perform types (RuntimeMetadata.shapeKindInWorld p.runtime ty)
    if kind != .closure then return none
    let .closure _ _ count ← RuntimeArrayQueries.perform types
      (CompilerFactAdapters.castTypeInfoInWorld p.lifecycle.calls.symbols.facts ty)
      | throw (.unsupported "closure source constructor mismatch")
    pure (some count)
  llvmLinkName := fun callee => do
    let some name ← lift (CompilerCallFacts.codegenSymbolName p.intrinsics callee)
      | throw (.invalidProgram "source LLVM intrinsic requires a codegen symbol_name attribute")
    pure name }
end Miri.Input.CompilerExecutionCallLeaves
