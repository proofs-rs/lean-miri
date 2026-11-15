import Miri.Input.Model.SourceSymbols

/-! Typed finite declaration facts. No JSON syntax, executable MIR, compiler
query result or evaluation-local handle is stored in these records. -/
namespace Miri.Input.SourceDeclarations

inductive ItemKind where
  | function | associatedFunction
  deriving Repr, DecidableEq

/-- Declaration attributes/lang-item role, not an instance-resolution answer.
Unknown source evidence never defaults to an ordinary Item selection. -/
inductive ItemRole where
  | ordinary | intrinsic | dropGlue | foreign | unavailable
  deriving Repr, DecidableEq

structure ItemDeclaration where
  definition : DefinitionId
  path : String
  kind : ItemKind
  parameters : Array SourceSymbols.ParameterKind
  role : ItemRole := .unavailable
  deriving Repr, DecidableEq

structure Target where
  triple : String
  architecture : String
  dataLayout : String
  pointerSizeBits : Nat
  endian : String
  runtimeDataLayout : Option TargetDataLayoutEvidence := none
  deriving Repr, DecidableEq

structure GenericParameter where
  definition : DefinitionId
  index : Nat
  kind : SourceSymbols.ParameterKind
  deriving Repr, DecidableEq

/-- Lexical ownership, not a trait-implementation or selection answer. -/
structure GenericLayer where
  owner : DefinitionId
  parent : Option DefinitionId
  parentCount : Nat
  parameters : Array GenericParameter
  /-- Full ordered slot view projected once from the validated lexical chain.
  Original parameter identities (including Trait Self==owner) remain above. -/
  flattenedParameters : Array SourceSymbols.ParameterKind
  deriving Repr, DecidableEq

/-- Lookup the boundary-established slot view. No raw identity, parameter-kind
or lexical-chain validation is repeated at a demand-time query. -/
def fullParameters (layers : Array GenericLayer) (owner : DefinitionId) :
    Except String (Array SourceSymbols.ParameterKind) := do
  let some layer := layers.find? (·.owner == owner)
    | throw "typed source generic declaration unavailable"
  return layer.flattenedParameters

end Miri.Input.SourceDeclarations
