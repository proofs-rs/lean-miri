import duplicate_prefix.EmptyRootArguments

namespace DuplicatePrefix.DuplicatePrefixSliceArgument
open Miri Miri.ABI Miri.Memory Miri.Interpreter
noncomputable section

/-- The physical scalar-pair's first component can be pointer-encoded or an
integer with no provenance. In particular integer addresses are distinct from
wildcard-provenance pointers, even when their numeric addresses coincide. -/
inductive Argument where
  | pointer (value : Pointer Provenance)
  | integer (address : UInt64)
  deriving DecidableEq, Repr

def address : Argument → UInt64
  | .pointer value => value.offset.bytes
  | .integer value => value

def placePointer : Argument → Pointer (Option Provenance)
  | .pointer value => value.withOptionalProvenance
  | .integer value => Pointer.withoutProvenance value

/-- Raw scalar-pair encoding consumed by the actual reference argument logic.
This is a representation definition, with no validity or resolution premise. -/
def rawValue (target : TargetDataLayout) (argument : Argument) (len : UInt64)
    (layout : LocalLayout) : RvalueImmTy Provenance :=
  match argument with
  | .pointer value => RetagReferencePlace.sliceValue target value len layout
  | .integer value => RetagReferencePlace.integerSliceValue value len layout

def first (target : TargetDataLayout) (argument : Argument) (len : UInt64) : OpTy Provenance :=
  ⟨.immediate (rawValue target argument len ActualReferenceMetadata.reference).imm,
    ActualReferenceMetadata.reference⟩

theorem pointer_value (target : TargetDataLayout) (pointer : Pointer Provenance)
    (len : UInt64) (layout : LocalLayout) :
    rawValue target (.pointer pointer) len layout = RetagReferencePlace.sliceValue target pointer len layout := rfl

theorem integer_value (target : TargetDataLayout) (value len : UInt64) (layout : LocalLayout) :
    rawValue target (.integer value) len layout = RetagReferencePlace.integerSliceValue value len layout := rfl

/-- Existing no-provenance empty-reference proofs encode precisely this
integer branch; no conversion to wildcard provenance is involved. -/
theorem integer_first_zero (target : TargetDataLayout) (value : UInt64) :
    first target (.integer value) 0 = EmptyRootArguments.first value := rfl

theorem integer_without_provenance (value : UInt64) :
    (placePointer (.integer value)).provenance = none := rfl

theorem pointer_preserves_provenance (pointer : Pointer Provenance) :
    (placePointer (.pointer pointer)).provenance = some pointer.provenance := rfl

theorem integer_ne_wildcard (value : UInt64) :
    Argument.integer value ≠ .pointer (Pointer.new .wildcard (Size.ofBytes value)) := by
  intro same
  cases same

end
end DuplicatePrefix.DuplicatePrefixSliceArgument
