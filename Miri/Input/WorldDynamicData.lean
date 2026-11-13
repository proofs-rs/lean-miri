import Miri.Input.RuntimeArrayTypes
import Miri.Input.WorldDynamicSource

/-! Compiler-World adapters for checked Dynamic source transport. -/
namespace Miri.Input.WorldDynamicData
open Miri.Interpreter GenericSubstitution TraitSelection
abbrev View := WorldDynamicSource.View
abbrev ofWorld := WorldDynamicSource.ofWorld
private def lift (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error error => throw error

def query (fuel : Nat) (owner : Miri.MIR.TyId) : RuntimeArrayTypes.CompilerM (Option View) := do
  RuntimeArrayTypes.liftType (WorldDynamicSource.query (← get).metadata fuel owner)

/-- A consumer rereads the owner in the current execution World. The payload is
an ephemeral view, never a transferable compiler-session/global token. -/
def validate (fuel : Nat) (view : View) : RuntimeArrayTypes.CompilerM Unit := do
  unless (← query fuel view.owner) == some view do
    throw "typed dynamic runtime bridge: owner/payload differs from current World"

/-- Exact outer region-binder opening, then erasure for the first-slot query.
Nested binders retain their own variables; type/const binders reject above. -/
def principalRef (fuel : Nat) (view : View) : RuntimeArrayTypes.CompilerM TraitRef := do
  validate fuel view
  let some predicate := view.principal | throw "object method candidate requires a principal"
  let .trait definition arguments := predicate.body | throw "principal is not a trait"
  let world ← get
  let selfTerm ← lift (GenericInstantiationWorld.ofType world.arena fuel view.owner)
  let arguments ← lift (GenericInstantiationWorld.ofArguments world.arena fuel arguments)
  let arguments ← lift (arguments.mapM fun term => do
    let opened ← Universes.openTerm predicate.variables 1 fuel 0 term
    BinderRegions.eraseAndAnonymize fuel opened)
  pure ⟨definition,#[selfTerm] ++ arguments⟩

/-- Physical trait definition conversion is distinct from the legacy runtime
principal, which is a predicate handle rather than a DefinitionRef. -/
def principalDefinition (fuel : Nat) (view : View) :
    RuntimeArrayTypes.CompilerM (Option DefinitionRef) := do
  validate fuel view
  let some predicate := view.principal | return none
  let .trait definition _ := predicate.body | throw "dynamic principal is not a trait"
  some <$> lift ((← get).arena.definitionRef definition)

/-- Material predicate IDs remain unchanged. Constructed predicates receive
real checked handles in this execution World's append-only predicate arena. -/
def runtimeData (fuel : Nat) (owner : Miri.MIR.TyId) :
    RuntimeArrayTypes.CompilerM (Option VirtualCalls.DynamicData) := do
  RuntimeArrayTypes.liftType (WorldDynamicSource.runtimeData (← get).metadata fuel owner)

/-- Unported result-catalog leaves may consume only their real immutable
prefix. A valid suffix handle must never be dropped or reinterpreted as a row. -/
def requireMaterialPredicates (values : PredicateList) : RuntimeArrayTypes.CompilerM Unit := do
  let world ← get
  for id in values do
    let _ ← lift (world.arena.existential id)
    unless id < world.arena.materialPredicates.size do
      throw "constructed runtime predicate requires source vtable comparison/normalization/allocation"

def requireMaterialPrincipal (principal : Option Nat) : RuntimeArrayTypes.CompilerM Unit := do
  let some id := principal | return ()
  requireMaterialPredicates #[id]
  let predicate ← lift ((← get).arena.existential id)
  let .trait .. := predicate.body | throw "vtable principal predicate is not a trait"

def requireMaterialType (id : Miri.MIR.TyId) : RuntimeArrayTypes.CompilerM Unit := do
  let .material _ ← lift ((← get).arena.lookupType id)
    | throw "constructed type requires source vtable query"
  pure ()

end Miri.Input.WorldDynamicData
