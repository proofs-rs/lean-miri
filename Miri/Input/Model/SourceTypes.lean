import Miri.Input.Model.SourceDeclarations
import Miri.ABI.ExternAbi

/-! Typed finite source syntax, not compiler layout/query answers. References
address the original source tables; canonical runtime handles are allocated only
by demand operations. Unsupported tags remain explicit errors when demanded. -/
namespace Miri.Input.SourceTypes
abbrev TypeRef := Nat
abbrev DefinitionRef := Nat

inductive BoundRegionKind where
  | anonymous | named (definition : DefinitionRef)
  | namedForPrinting (name : String) | closureEnvironment
  deriving Repr, DecidableEq
inductive Region where
  | static | erased
  | earlyParameter (index : Nat)
  | bound (debruijn slot : Nat) (kind : BoundRegionKind)
  | unsupported (tag : String)
  deriving Repr, DecidableEq
inductive BoundVariable where
  | region (kind : BoundRegionKind)
  | unsupported (tag : String)
  deriving Repr, DecidableEq
structure Signature where
  inputs : Array TypeRef
  output : TypeRef
  safety : MIR.Safety
  abi : ABI.ExternAbi
  cVariadic : Bool
  boundVariables : Array BoundVariable
  deriving Repr, DecidableEq

inductive ConstExpr where
  | parameter (index : Nat) (typeRef : Option TypeRef)
  | value (typeRef : TypeRef) (bits sizeBytes : Nat)
  | alias (reference : Nat)
  | unsupported (tag : String)
  deriving Repr, DecidableEq
inductive Argument where
  | type (typeRef : TypeRef)
  | lifetime (region : Region)
  | constant (value : ConstExpr)
  deriving Repr, DecidableEq
/-- A source const alias remains unevaluated syntax. References use this same
immutable type/definition universe, not canonical runtime handles. -/
structure ConstantAlias where
  rigid : Bool
  kind : MIR.ConstAliasKind
  definition : DefinitionRef
  typeRef : TypeRef
  arguments : Array Argument
  /-- Target-usize result joined from a validated exact ground compiler key. -/
  usizeValue : Option Nat := none
  deriving Repr, DecidableEq
/-- Original range-bound syntax. An unevaluated bound is not its value. -/
inductive PatternBound where
  | constant (expression : ConstExpr)
  | alias (rigid : Bool) (kind : MIR.ConstAliasKind) (definition : DefinitionRef) (arguments : Array Argument)
  deriving Repr, DecidableEq
inductive ExistentialPredicate where
  | trait (definition : DefinitionRef) (arguments : Array Argument) (boundVariables : Array BoundVariable)
  | projection (definition parentTrait : DefinitionRef) (arguments : Array Argument)
      (term : TypeRef) (boundVariables : Array BoundVariable)
  | autoTrait (definition : DefinitionRef) (boundVariables : Array BoundVariable)
  | unsupported (tag : String)
  deriving Repr, DecidableEq
structure Closure where
  definition : DefinitionRef
  parentDefinition : DefinitionRef
  parentCount : Nat
  arguments : Array Argument
  kindType : TypeRef
  signatureType : TypeRef
  tupledUpvarsType : TypeRef
  deriving Repr, DecidableEq

inductive Expr where
  | primitive (kind name : String)
  | parameter (index : Nat) (name : String)
  | array (element : TypeRef) (length : ConstExpr)
  | tuple (elements : Array TypeRef)
  | rawPointer (pointee : TypeRef) (mutability : MIR.Mutability)
  | reference (pointee : TypeRef) (mutability : MIR.Mutability) (region : Region)
  | patternNotNull (base : TypeRef)
  | patternRange (base : TypeRef) (start end_ : PatternBound)
  | nominal (definition : DefinitionRef) (arguments : Array Argument)
  | dynamicObject (region : Region) (predicates : Array ExistentialPredicate)
  | functionPointer (signature : Signature)
  | functionDefinition (definition : DefinitionRef) (arguments : Array Argument)
  /-- Unnormalized associated type source; retaining it proves no value/layout. -/
  | projectionAlias (definition parentTrait : DefinitionRef) (arguments : Array Argument)
  | closure (source : Closure)
  | unsupported (tag : String)
  deriving Repr, DecidableEq

inductive Discriminant where
  | relative (distance : Nat) | explicit (definition : DefinitionRef) | absent
  deriving Repr, DecidableEq
structure Field where
  index : Nat
  definition : Option DefinitionRef
  name : String
  typeRef : TypeRef
  deriving Repr, DecidableEq
structure Constructor where
  definition : DefinitionRef
  kind : String
  deriving Repr, DecidableEq
structure Variant where
  index : Nat
  definition : Option DefinitionRef
  name : String
  constructor : Option Constructor
  fields : Array Field
  fieldsNonExhaustive : Option Bool
  discriminant : Discriminant
  deriving Repr, DecidableEq
structure Adt where
  kind : AdtKind
  representation : ReprOptions
  parameters : Array SourceSymbols.ParameterKind
  variants : Array Variant
  variantsNonExhaustive : Option Bool
  deriving Repr, DecidableEq
structure Definition where
  raw : DefinitionId
  kind : String
  path : String
  adt : Option Adt
  traitIsAuto : Option Bool := none
  deriving Repr, DecidableEq

structure MetadataStruct where
  definition : DefinitionRef
  representation : ReprOptions
  fieldCount : Nat
  argumentCount : Nat
  deriving Repr, DecidableEq
inductive MetadataPointer where
  | notNullRawForeign (mutable : Bool) (pointee : DefinitionRef)
  | unsupported (kind pattern base pointee : String)
  deriving Repr, DecidableEq
structure DynMetadataDeclarations where
  metadataType : DefinitionRef
  pointeeTrait : DefinitionRef
  metadataParent : DefinitionRef
  pointeeParameterCount : Nat
  metadataParameterCount : Nat
  dynamic : MetadataStruct
  dynamicParameterCount : Nat
  vtableField : Nat
  phantomField : Nat
  nonnull : MetadataStruct
  nonnullLangItem : String
  pointer : MetadataPointer
  phantom : MetadataStruct
  phantomLangItem : String
  phantomParameterIndex : Nat
  deriving Repr, DecidableEq
inductive DynMetadata where
  | declarations (source : DynMetadataDeclarations)
  | metadataLangItemAbsent
  | unsupported (tag : String)
  deriving Repr, DecidableEq

structure Material where
  types : Array Expr
  definitions : Array Definition
  dynMetadata : Option DynMetadata
  constantAliases : Array ConstantAlias := #[]
  deriving Repr, DecidableEq

structure Projection (α : Type) where
  definition : DefinitionRef
  parentTrait : DefinitionRef
  arguments : Array α
  term : α
  deriving Repr
structure Existential (α : Type) where
  region : MIR.Region
  principal : Option DefinitionRef
  arguments : Array α
  projections : Array (Projection α)
  autoTraits : Array DefinitionRef
  deriving Repr

/-- Monomorphic source types keep definition references in the immutable source
universe. They are not canonical runtime type IDs. -/
inductive Concrete where
  | primitive (kind name : String)
  | array (element : Concrete) (length : Nat)
  | tuple (elements : Array Concrete)
  | pointer (kind : String) (pointee : Concrete)
  | patternNotNull (base : Concrete)
  | patternRange (base : Concrete) (start finish : Nat)
  | nominal (definition : DefinitionRef) (arguments : Array Concrete)
  | dynamicObject (source : Existential Concrete)
  | functionPointer (inputs : Array Concrete) (output : Concrete)
      (safety : MIR.Safety) (abi : ABI.ExternAbi) (cVariadic : Bool)
  | closure (definition : DefinitionRef) (arguments : Array Concrete)
  deriving Repr
end Miri.Input.SourceTypes
