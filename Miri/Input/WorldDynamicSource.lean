import Miri.Input.RuntimeMetadata
import Miri.Input.SourceDynamicView
import Miri.Interpreter.VirtualCalls

/-! Execute checked Dynamic source transport in the current type universe. -/
namespace Miri.Input.WorldDynamicSource
open Miri.Interpreter GenericSubstitution TraitSelection
abbrev View := SourceDynamicView.View
abbrev ofWorld := SourceDynamicView.ofWorld
private def lift (result : Except String α) : TypeArena.WorldM α :=
  match result with | .ok value => pure value | .error error => throw error

def query (metadata : RuntimeMetadata) (fuel : Nat) (owner : Miri.MIR.TyId) :
    TypeArena.WorldM (Option View) := do
  lift (SourceDynamicView.query metadata.normalizationContext fuel (← get) owner)

/-- Prefix handles are preserved; constructed source predicates are checked and
interned in the same execution-owned suffix, including the actual principal. -/
def runtimeData (metadata : RuntimeMetadata) (fuel : Nat) (owner : Miri.MIR.TyId) :
    TypeArena.WorldM (Option VirtualCalls.DynamicData) := do
  match ← lift ((← get).lookupType owner) with
  | .material node =>
    match node.shape with
    | .dynamicTraitObject predicates principal _ => return some ⟨predicates,principal⟩
    | _ => return none
  | .constructed (.dynamic _) =>
    let some view ← query metadata fuel owner | throw "dynamic owner source shape changed"
    let mut predicates := #[]
    let mut principal := none
    for predicate in view.value.predicates do
      let handle ← TypeArena.World.internExistential predicate fuel
      predicates := predicates.push handle
      if let .trait .. := predicate.body then principal := some handle
    return some ⟨predicates,principal⟩
  | .constructed _ => return none

end Miri.Input.WorldDynamicSource
