import Miri.Input.Model
import Miri.Input.SourceEnvironment

/-! Execution-local declaration predicate lookup. Only source-explicit clauses
and the trait self-clause are assembled; inferred outlives remain a separate
compiler rule and are never silently classified as discharged obligations. -/
namespace Miri.Input.SourceEnvironmentRuntime
open GenericSubstitution TraitSelection

def lookupDefinitions (definitions : Array DefinitionId) : SourceEnvironment.Lookup := fun identity => do
  let mut result := none
  for definition in definitions do
    if definition.crateIndex == identity.crateIndex && definition.index == identity.index then
      unless result.isNone do throw "duplicate physical source environment identity"
      let some material := definition.sourceEnvironment
        | throw "raw source environment declaration is absent"
      result := some material
  let some material := result | throw "source environment physical definition is absent"
  pure material

def lookup (document : ImportDocument) : SourceEnvironment.Lookup :=
  lookupDefinitions document.definitions

/-- Instantiate source obligations for an arbitrary argument vector in this
input's physical definition namespace. This does not run trait selection. -/
def instantiate (document : ImportDocument) (fuel : Nat) (identity : DefinitionIdentity)
    (arguments : Array Term) : Except String (Array Clause) :=
  SourceEnvironment.instantiate (lookup document) fuel identity arguments

end Miri.Input.SourceEnvironmentRuntime
