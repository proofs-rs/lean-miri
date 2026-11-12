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
  | positive | negative
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
  expression : Option DefinitionTemplate
  requiresHiddenTypeInference : Bool
  hasValue : Bool := true
  /-- Source RHS was retained by declaration dependency slicing; absence is Unsupported. -/
  materialRetained : Bool := true
  deriving Repr, DecidableEq

structure AssociatedMethod where
  traitAssociatedDefinition : DefinitionIdentity
  implementationDefinition : DefinitionIdentity
  isFinal : Bool
  deriving Repr, DecidableEq

structure TraitMember where
  definition : DefinitionIdentity
  kind : String
  hasValue : Bool
  isFinal : Bool
  isMethod : Bool
  isImplTraitInTrait : Bool
  deriving Repr, DecidableEq

structure Impl where
  definition : DefinitionIdentity
  parameters : Array ArgSort
  traitRef : TraitRef
  polarity : Polarity
  isDefault : Bool
  associatedValues : Array AssociatedValue
  methods : Array AssociatedMethod := #[]
  constants : Array AssociatedMethod := #[]
  deriving Repr, DecidableEq

inductive BuiltinTrait where
  | sized | metaSized | pointeeSized | freeze | unpin | unsafeUnpin | copy | clone
  | fn | fnMut | fnOnce | unsize | coerceUnsized | dispatchFromDyn
  deriving Repr, DecidableEq, BEq

structure TraitDeclaration where
  definition : DefinitionIdentity
  parameters : Array ArgSort
  isAuto : Bool
  isAlias : Bool
  isUnsafe : Bool
  isCoinductive : Bool
  isMarker : Bool
  langItem : Option String
  superPredicates : Array Clause
  implementations : Array Impl
  members : Array TraitMember := #[]
  deriving Repr, DecidableEq

/-- Source LangItem symbols are semantic declaration identities, not type
spelling. Unknown language traits still require an explicit builtin provider. -/
def TraitDeclaration.builtin (value : TraitDeclaration) : Option BuiltinTrait :=
  match value.langItem with
  | some "sized" => some .sized | some "meta_sized" => some .metaSized
  | some "pointee_sized" => some .pointeeSized | some "freeze" => some .freeze
  | some "unpin" => some .unpin | some "unsafe_unpin" => some .unsafeUnpin
  | some "copy" => some .copy | some "clone" => some .clone
  | some "fn" => some .fn | some "fn_mut" => some .fnMut | some "fn_once" => some .fnOnce
  | some "unsize" => some .unsize | some "coerce_unsized" => some .coerceUnsized
  | some "dispatch_from_dyn" => some .dispatchFromDyn
  | _ => none

structure Program where
  traits : Array TraitDeclaration
  /-- `none` retains all source impls. A closed scope filters only concrete
  root-Self ADT impls and requires every query constructor to remain in scope. -/
  constructorScope : Option (Array DefinitionIdentity) := none
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
