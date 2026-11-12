import Miri.Input.GenericSubstitution

/-! Declaration material for trait selection. These records contain trait/impl
heads, generic parameters and source predicates, never selected-instance or
per-goal solver answers. Specialization-parent relations are deliberately absent:
they must be derived by the Lean solver, rather than exported from rustc's
specialization graph. Source captures must enumerate the complete impl catalog
for every included trait; an absent catalog is not a negative trait result. -/
namespace Miri.Input.TraitSelection
open GenericSubstitution

inductive Polarity where
  | positive | negative | reservation
  deriving Repr, DecidableEq, BEq

structure TraitRef where
  definition : DefinitionIdentity
  arguments : Array Term
  deriving Repr, DecidableEq, BEq

structure Goal where
  polarity : Polarity
  traitRef : TraitRef
  deriving Repr, DecidableEq, BEq

inductive AliasTermKind where
  | projectionType | inherentType | opaqueType | freeType
  | anonymousConst | projectionConst | freeConst | inherentConstSelf | inherentConstImpl
  deriving Repr, DecidableEq, BEq

inductive Predicate where
  | trait (goal : Goal)
  | equal (left right : Term)
  | projection (kind : AliasTermKind) (associated : DefinitionIdentity) (arguments : Array Term) (expected : Term)
  | regionOutlives (longer shorter : Term)
  | typeOutlives (ty region : Term)
  | constEvaluatable (value : Term)
  | constHasType (value ty : Term)
  | wellFormed (value : Term)
  | hostEffect (requiresConst : Bool) (traitRef : TraitRef)
  | unstableFeature (feature : String)
  deriving Repr, DecidableEq, BEq

structure Clause where
  variables : Array BoundVariable
  predicate : Predicate
  deriving Repr, DecidableEq, BEq

structure AssociatedValue where
  traitAssociatedDefinition : DefinitionIdentity
  implementationDefinition : DefinitionIdentity
  expression : DefinitionTemplate
  ownPredicates : Array Clause
  deriving Repr, DecidableEq

structure Impl where
  definition : DefinitionIdentity
  parameters : Array ArgSort
  traitRef : TraitRef
  polarity : Polarity
  isDefault : Bool
  predicates : Array Clause
  associatedValues : Array AssociatedValue
  deriving Repr, DecidableEq

inductive BuiltinTrait where
  | sized | freeze | unpin | unsafeUnpin | copy | clone
  | fn | fnMut | fnOnce | unsize | coerceUnsized | dispatchFromDyn
  deriving Repr, DecidableEq, BEq

structure TraitDeclaration where
  definition : DefinitionIdentity
  parameters : Array ArgSort
  isAuto : Bool
  isUnsafe : Bool
  isCoinductive : Bool
  isMarker : Bool
  builtin : Option BuiltinTrait
  superPredicates : Array Clause
  implementations : Array Impl
  deriving Repr, DecidableEq

structure Program where
  traits : Array TraitDeclaration
  deriving Repr, DecidableEq

structure Environment where
  assumptions : Array Clause := #[]
  /-- The initial executable domain ignores regions only when the requesting
  compiler query explicitly erases them. Other environments require relations. -/
  eraseRegions : Bool := false
  deriving Repr, DecidableEq

structure ImplSelection where
  implementation : DefinitionIdentity
  substitution : Array Term
  deriving Repr, DecidableEq, BEq

end Miri.Input.TraitSelection
