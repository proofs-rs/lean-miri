import Miri.Input.Model.SourceMir
/-! Exact concrete compiler-CTFE observations. Results are trusted compiler
outputs, not a Lean evaluation of generic const source. Missing keys are unknown. -/
namespace Miri.Input.SourceConstValues
inductive Value where
  | scalar (bits sizeBytes : Nat)
  | zeroSized
  deriving Repr, DecidableEq
structure Row where
  definition : DefinitionId
  arguments : Array SourceTypes.Argument
  promoted : Option Nat
  typeRef : SourceTypes.TypeRef
  value : Value
  deriving Repr, DecidableEq
structure Material where
  rows : Array Row
  deriving Repr, DecidableEq
end Miri.Input.SourceConstValues
