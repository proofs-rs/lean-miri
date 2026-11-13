import Miri.Input.GenericSubstitution

/-! Raw scalar-u64 CTFE source syntax, including physical external constant
references. This model provides no source admission, allocation, interpreter,
query memo or compiler-result capability. Preambles remain explicit. -/
namespace Miri.Input.RawU64Frame
open GenericSubstitution
inductive OwnerKind where
  | constant | associatedConstant | anonymousConstant
  deriving Repr, DecidableEq
inductive ValueClass where
  | typeValue | literalValue
  deriving Repr, DecidableEq
structure SourceValue where
  kind : ValueClass
  span : MIR.SpanRef
  userType : Option Nat
  value : UInt64
  deriving Repr, DecidableEq
structure Reference where
  definition : DefinitionIdentity
  arguments : Array Term
  span : MIR.SpanRef
  userType : Option Nat
  deriving Repr, DecidableEq
inductive Operand where
  | copy (slot : Nat) | move (slot : Nat)
  | sourceValue (source : SourceValue) | constant (source : Reference)
  deriving Repr, DecidableEq
inductive Rvalue where
  | use (source : Operand) (retag : Bool)
  | unaryNot (source : Operand)
  deriving Repr, DecidableEq
inductive Statement where
  | live (slot : Nat) | dead (slot : Nat)
  | assign (slot : Nat) (value : Rvalue)
  | counter | nop
  deriving Repr, DecidableEq
/-- All locals have the explicit admitted u64 source type. This program is
one non-cleanup block ending in Return; header/source metadata stays in the
common CtfeMirSource.Source. Physical references never assume crate0. -/
structure Program where
  ownerKind : OwnerKind
  defPath : String
  preambleDefSpan : MIR.SpanRef
  localCount : Nat
  required : Array Reference
  statements : Array Statement
  deriving Repr, DecidableEq

def validate (program : Program) : Except String Unit := do
  unless program.localCount > 0 do throw "raw u64 source lacks return place"
  let slot (index : Nat) := do
    unless index < program.localCount do throw "raw u64 source local out of bounds"
  let operand : Operand → Except String Unit
    | .copy index | .move index => slot index
    | .sourceValue source => unless source.userType.isNone do throw "raw u64 source annotation material absent"
    | .constant reference => unless reference.userType.isNone do throw "raw u64 constant annotation material absent"
  for statement in program.statements do
    match statement with
    | .live index | .dead index =>
      slot index
      unless index != 0 do throw "raw u64 storage marker on return place"
    | .assign index (.use source _) | .assign index (.unaryNot source) => slot index *> operand source
    | .counter | .nop => pure ()
end Miri.Input.RawU64Frame
