import Miri.Input.TraitSelection.Material

/-! Raw alias declaration metadata. RHS trees are shared through the existing
Definition.genericTemplate, not duplicated here. Associated type defaultness is
source material; inherited specialization choices are deliberately not exported. -/
namespace Miri.Input.AliasMaterial
open GenericSubstitution
open TraitSelection (Clause)

inductive Container where
  | trait
  | inherentImpl
  | traitImpl (traitItem : DefinitionIdentity)
  deriving Repr, DecidableEq
inductive Kind where
  | free (isChecked : Bool)
  | associated (container : Container) (parent : DefinitionIdentity)
      (parentParameterCount : Nat) (isFinal : Bool)
  deriving Repr, DecidableEq
structure Declaration where
  definition : DefinitionIdentity
  kind : Kind
  hasValue : Bool
  deriving Repr, DecidableEq

end Miri.Input.AliasMaterial
