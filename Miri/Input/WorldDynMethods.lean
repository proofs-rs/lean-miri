import Miri.Input.RuntimeArrayTypes
import Miri.Input.SourceDynMethods

/-! World adapter for source-only own-method eligibility. -/
namespace Miri.Input.WorldDynMethods
open GenericSubstitution TraitSelection
abbrev ownMethods := SourceDynMethods.ownMethods

/-- Read declarations from the current execution-owned World. -/
def query (identity : DefinitionIdentity) (work fuel : Nat) : RuntimeArrayTypes.CompilerM (Array DefinitionIdentity) := do
  let world ← get
  match ownMethods world.metadata.normalizationContext work fuel identity with
  | .ok value => pure value
  | .error error => throw error

end Miri.Input.WorldDynMethods
