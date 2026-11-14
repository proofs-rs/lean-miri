import Miri.Input.TraitSelection.Material

/-! Canonical source generic-scope declarations. Parent identities and own
source-explicit predicates are material; inferred outlives are not included. -/
namespace Miri.Input.SourceEnvironment
open GenericSubstitution TraitSelection

structure Parent where
  definition : DefinitionIdentity
  parameterCount : Nat
  deriving Repr, DecidableEq

structure Material where
  parameters : Array ArgSort
  parent : Option Parent
  genericParent : Option Parent
  isTrait : Bool
  ownPredicates : Array Clause
  deriving Repr, DecidableEq

abbrev Lookup := DefinitionIdentity → Except String Material

end Miri.Input.SourceEnvironment
