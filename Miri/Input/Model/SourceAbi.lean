import Miri.Input.Model.SourceSymbolNames
import Miri.Input.Model.SourceDeclarations
import Miri.Input.Model.SourceTypes

/-! Finite ABI declaration syntax. This records original generic clauses and
signatures, not monomorphic ABI/selection answers. Unknown semantics are explicit
constructors and cannot be confused with an empty supported clause list. -/
namespace Miri.Input.SourceAbi

inductive BuiltinTrait where
  | sized | copy | metaSized
  deriving Repr, DecidableEq

structure BuiltinDeclaration where
  definition : DefinitionId
  role : BuiltinTrait
  pinnedCore : Bool := false
  deriving Repr, DecidableEq

inductive Clause where
  | trait (definition : DefinitionId) (role : Option BuiltinTrait) (arguments : Array SourceTypes.TypeRef)
  | projection (definition parentTrait : DefinitionId) (arguments : Array SourceTypes.TypeRef) (term : SourceTypes.TypeRef)
  | constHasType (parameter : Nat) (type : SourceTypes.TypeRef)
  | typeOutlives (type : SourceTypes.TypeRef) (region : SourceTypes.Region)
  | regionOutlives (longer shorter : SourceTypes.Region)
  | unsupported (kind : String)
  deriving Repr, DecidableEq

structure OwnerClauses where
  owner : DefinitionId
  parent : Option DefinitionId
  clauses : Array Clause
  deriving Repr, DecidableEq

structure ConstParameterType where
  definition : DefinitionId
  type : SourceTypes.TypeRef
  deriving Repr, DecidableEq

inductive TargetFeatureKind where
  | enabled | forced | implied | unsupported (kind : String)
  deriving Repr, DecidableEq
structure TargetFeature where
  name : String
  kind : TargetFeatureKind
  deriving Repr, DecidableEq

structure TargetFeatureDeclaration where
  definition : DefinitionId
  features : Array TargetFeature
  deriving Repr, DecidableEq

structure Attributes where
  neverUnwind : Bool
  trackCaller : Bool
  foreignItem : Bool
  dropGlue : Bool
  deriving Repr, DecidableEq

structure Function where
  definition : DefinitionId
  signature : SourceTypes.Signature
  attributes : Attributes
  constParameterTypes : Array ConstParameterType := #[]
  deriving Repr, DecidableEq

inductive SelfHead where
  | tuple (arity : Nat)
  | adt (definition : DefinitionId)
  | never
  | unsupported (tag : String)
  deriving Repr, DecidableEq

structure ImplHeader where
  definition : DefinitionId
  traitDefinition : DefinitionId
  argumentCount : Nat
  selfHead : SelfHead
  parameterCount : Nat
  genericParent : Option DefinitionId
  clauseCount : Nat
  clauseParent : Option DefinitionId
  positive : Bool
  nonConst : Bool
  final : Bool
  deriving Repr, DecidableEq

structure SuperTrait where
  definition : DefinitionId
  argumentCount : Nat
  selfParameter : Option Nat
  positive : Bool
  boundVariableCount : Nat
  deriving Repr, DecidableEq

/-- A complete finite ordinary-trait header domain, independent of a goal. -/
structure TraitDeclaration where
  definition : DefinitionId
  isAuto : Bool
  isMarker : Bool
  isCoinductive : Bool
  isSafe : Bool
  nonConst : Bool
  parameterCount : Nat
  hasSelf : Bool
  genericParent : Option DefinitionId
  complete : Bool
  superTraits : Array SuperTrait
  implementations : Array ImplHeader
  deriving Repr, DecidableEq

inductive CallableKind where
  | fn | fnMut | fnOnce
  deriving Repr, DecidableEq

/-- Validated pinned callable declaration identities; these are not impl selections. -/
structure CallableDeclaration where
  definition : DefinitionId
  kind : CallableKind
  output : Option DefinitionId
  deriving Repr, DecidableEq

inductive AutoTraitRole where
  | unpin | unsafeUnpin | freeze
  deriving Repr, DecidableEq
inductive AutoSelfHead where
  | pattern (base : AutoSelfHead) (kind : String)
  | adt (definition : DefinitionId)
  | functionDefinition (definition : DefinitionId)
  | closure (definition : DefinitionId)
  | coroutineClosure (definition : DefinitionId)
  | tuple (arity : Nat)
  | rigid (kind : String)
  | unknown
  deriving Repr, DecidableEq
structure AutoImplHeader where
  definition : DefinitionId
  selfHead : AutoSelfHead
  polarity : String
  deriving Repr, DecidableEq
structure AutoDeclaration where
  definition : DefinitionId
  langItem : Option AutoTraitRole
  isAuto : Bool
  isUnsafe : Bool
  hasSelf : Bool
  parameters : Array (Nat × Bool)
  associatedItems : Nat
  clauses : Array (Except String DefinitionId)
  complete : Bool
  implementations : Array AutoImplHeader
  deriving Repr, DecidableEq
structure AutoTraits where
  langItems : Array (AutoTraitRole × Option DefinitionId)
  declarations : Array AutoDeclaration
  deriving Repr, DecidableEq

/-- Complete direct super-clause declaration graph for object-bound exclusion.
Trait identity cannot change during argument normalization. Unsupported clause
kinds remain unavailable rather than being omitted from the closure proof. -/
structure ObjectTraitDeclaration where
  definition : DefinitionId
  superTraits : Array DefinitionId
  unsupportedSuperClauses : Array String
  deriving Repr, DecidableEq

structure Material where
  functions : Array Function
  owners : Array OwnerClauses
  builtins : Array BuiltinDeclaration
  panicUnwinds : Bool
  panicInDropUnwinds : Bool
  traits : Array TraitDeclaration := #[]
  callables : Array CallableDeclaration := #[]
  autoTraits : Option AutoTraits := none
  optimizationDisabled : Bool := false
  objectTraits : Array ObjectTraitDeclaration := #[]
  symbolNames : Option SourceSymbolNames.Material := none
  targetFeatureDeclarations : Array TargetFeatureDeclaration := #[]
  callerIncremental : Option Bool := none
  deriving Repr, DecidableEq

end Miri.Input.SourceAbi
