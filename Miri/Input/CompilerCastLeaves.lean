import Miri.Input.CompilerProviders
import Miri.Interpreter.ExecutionCast

/-! Direct cast query construction. Unexported generic/trait transformations
remain named mandatory compiler queries, rather than a baseline CastHooks
record containing physical operations that will subsequently be overwritten. -/
namespace Miri.Input.CompilerCastLeaves
open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR
structure Required (S C : Type) where
  requireNoBoundVars : C → Array GenericArg → RvalueM S Unit
  resolveFunction : C → DefId → Array GenericArg → RvalueM S (Option CallInstance)
  resolveClosureFnOnce : C → DefId → Array GenericArg → RvalueM S CallInstance
  lockstepTails : C → TyId → TyId → RvalueM S (TyId × TyId)
  boxLayout : C → TyId → RvalueM S (TyAndLayout TyId)
  principal : C → PredicateList → RvalueM S (Option Nat)
  supertraitSlot : C → TyId → TyId → RvalueM S (Option Nat)
  eraseSelfTraitRef : C → Nat → RvalueM S Nat
  normalizePrincipal : C → PredicateList → RvalueM S (Option Nat)

def make (p : CompilerProviders.Prepared) (types : RuntimeArrayQueries.Access S) (required : Required S C)
    (vtable : VTableHooks Provenance S C CallInstance (FnAbi TyId))
    (expose : C → Provenance → RvalueM S Unit)
    (fromExposed : C → UInt64 → RvalueM S (Pointer (Option Provenance)))
    (validateABI : Immediate Provenance → LayoutData → Except StepError Unit) :
    ExecutionCast.Leaves S C :=
  let facts := p.lifecycle.calls.symbols.facts
  let context := facts.context
  let run := fun {A} (action : TypeArena.WorldM A) => RuntimeArrayQueries.perform types action
  { typeInfo := fun _ ty => run (CompilerFactAdapters.castTypeInfoInWorld facts ty)
    layoutOf := fun _ ty => run (CompilerFacts.layoutOfInWorld context ty)
    exposeProvenance := expose
    pointerFromExposedAddress := fromExposed
    usizeLayout := fun _ => run do
      CompilerFacts.layoutOfInWorld context (← CompilerFacts.primitiveTypeInWorld context "usize")
    ensureMonomorphic := fun _ ty => do
      unless ← run (CompilerFacts.booleanInWorld context ty "is_monomorphic_enough") do
        throw (.invalidProgram "compiler type still requires instantiation")
    requireNoBoundVars := required.requireNoBoundVars
    resolveFunction := required.resolveFunction
    resolveClosureFnOnce := required.resolveClosureFnOnce
    builtinDeref := fun _ ty explicit => run (CompilerFacts.builtinDerefInWorld context ty explicit)
    boxLayout := required.boxLayout
    validateImmediateABI := validateABI
    fieldLayout := fun _ parent index => run (RuntimeMetadata.fieldLayoutForInWorld context.runtime parent index)
    lockstepTails := required.lockstepTails
    vtableType := VTable.getPtrVTableType vtable
    vtablePointer := VTable.getPointer vtable
    principal := required.principal
    vtableEntries := vtable.entries
    supertraitSlot := required.supertraitSlot
    eraseSelfTraitRef := required.eraseSelfTraitRef
    normalizePrincipal := required.normalizePrincipal }
end Miri.Input.CompilerCastLeaves
